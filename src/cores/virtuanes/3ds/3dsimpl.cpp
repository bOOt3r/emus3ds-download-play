#include <unistd.h>
#include <string.h>
#include <stdio.h>
#include <3ds.h>

#include <dirent.h>

#include "3dstypes.h"
#include "3dsemu.h"
#include "3dsexit.h"
#include "3dsgpu.h"
#include "3dssound.h"
#include "3dsui.h"
#include "3dsinput.h"
#include "3dsfiles.h"
#include "3dsinterface.h"
#include "3dsmain.h"
#include "3dsasync.h"
#include "3dsimpl.h"
#include "3dsopt.h"
#include "3dsconfig.h"
#include "3dsdbg.h"
#include "3dsvideo.h"

#include "3dsimpl.h"
#include "3dsimpl_gpu.h"
#include "shaderfast2_shbin.h"
#include "shaderslow_shbin.h"
#include "shaderslow2_shbin.h"

#include "MMU.h"
#include "APU.h"
#include "PPU.h"
#include "ROM.h"
#include "NES.h"
#include "Pad.h"
#include "Config.h"
#include "palette.h"

#define SETTINGS_ALLSPRITES         0
#define SETTINGS_GLOBALINSERTCOIN1  1
#define SETTINGS_GLOBALINSERTCOIN2  2 
#define SETTINGS_INSERTCOIN1        3
#define SETTINGS_INSERTCOIN2        4  

#define MP_WLAN_COMM_ID  0x5A463250
#define MP_DATA_CHANNEL  1
#define MP_MAX_NODES     2
#define MP_SCAN_BUF_SIZE 0x4000
#define MP_MAX_DISCOVERED 8
#define MP_GAME_NAME_MAX 96
#define MP_LOBBY_VERSION 1

struct MpLobbyAppData
{
    char magic[4];
    u8 version;
    char gameName[MP_GAME_NAME_MAX];
};


enum MpPacketType
{
    MP_PACKET_MANIFEST      = 1,
    MP_PACKET_MANIFEST_ACK  = 2,
    MP_PACKET_ROM_CHUNK     = 3,
    MP_PACKET_ROM_CHUNK_ACK = 4,
    MP_PACKET_ROM_READY     = 5,
    MP_PACKET_ROM_ERROR     = 6,
    MP_PACKET_START_REQUEST = 7,
    MP_PACKET_START_READY   = 8,
    MP_PACKET_GO            = 9,
    MP_PACKET_GO_ACK        = 10,
    MP_PACKET_P2_INPUT          = 11,
    MP_PACKET_SYNC_INPUT        = 12,
    MP_PACKET_STATE_MANIFEST    = 13,
    MP_PACKET_STATE_MANIFEST_ACK = 14,
    MP_PACKET_STATE_CHUNK       = 15,
    MP_PACKET_STATE_CHUNK_ACK   = 16,
    MP_PACKET_STATE_READY       = 17,
    MP_PACKET_STATE_ERROR = 18,
    MP_PACKET_SYNC_REQUEST = 19
};

#define MP_ROM_CHUNK_SIZE 1024

#define MP_HOST_STATE_PATH   "sdmc:/virtuanes_localplay_host.state"
#define MP_CLIENT_STATE_PATH "sdmc:/virtuanes_localplay_session.state"
#define MP_ROM_PATH_MAX   512

struct MpPacketHeader
{
    char magic[4];
    u8 version;
    u8 type;
    u16 payloadSize;
};

struct MpManifestPacket
{
    MpPacketHeader header;
    u32 romSize;
    u32 romCrc32;
    char gameName[MP_GAME_NAME_MAX];
};

struct MpManifestAckPacket
{
    MpPacketHeader header;
};

struct MpRomChunkPacket
{
    MpPacketHeader header;
    u32 chunkIndex;
    u32 offset;
    u16 dataSize;
    u8 data[MP_ROM_CHUNK_SIZE];
};

struct MpRomChunkAckPacket
{
    MpPacketHeader header;
    u32 chunkIndex;
};

struct MpRomReadyPacket
{
    MpPacketHeader header;
    u32 romSize;
    u32 romCrc32;
};

struct MpRomErrorPacket
{
    MpPacketHeader header;
};


struct MpStartPacket
{
    MpPacketHeader header;
    u32 token;
};


struct MpP2InputPacket
{
    MpPacketHeader header;
    u32 sequence;
    u8 buttons;
};

struct MpSyncInputPacket
{
    MpPacketHeader header;
    u32 sequence;
    u16 buttons;
};

struct MpSyncRequestPacket
{
    MpPacketHeader header;
    u32 sequence;
};


struct MpStateManifestPacket
{
    MpPacketHeader header;
    u32 token;
    u32 stateSize;
    u32 stateCrc32;
};

struct MpStateManifestAckPacket
{
    MpPacketHeader header;
    u32 token;
};

struct MpStateChunkPacket
{
    MpPacketHeader header;
    u32 token;
    u32 chunkIndex;
    u32 offset;
    u16 dataSize;
    u8 data[MP_ROM_CHUNK_SIZE];
};

struct MpStateChunkAckPacket
{
    MpPacketHeader header;
    u32 token;
    u32 chunkIndex;
};

struct MpStateReadyPacket
{
    MpPacketHeader header;
    u32 token;
    u32 stateSize;
    u32 stateCrc32;
};

struct MpStateErrorPacket
{
    MpPacketHeader header;
    u32 token;
};


static const char mpPassphrase[] = "zf2-local-poc";

static udsBindContext mpBindCtx;
static bool mpUdsInitialized = false;
static bool mpHostActive = false;
static bool mpClientActive = false;
static u32 mpRemoteKeys = 0;

static udsNetworkStruct mpDiscoveredNetworks[MP_MAX_DISCOVERED];
static int mpDiscoveredCount = 0;


static char mpHostGameName[MP_GAME_NAME_MAX] = {};
static u32 mpHostRomSize = 0;

static bool mpManifestAcked = false;
static int mpManifestSendCounter = 0;

static bool mpClientManifestReceived = false;

static char mpHostRomPath[MP_ROM_PATH_MAX] = {};
static u32 mpHostRomCrc32 = 0;

static FILE *mpHostTransferFile = NULL;
static u32 mpHostTransferOffset = 0;
static u32 mpHostChunkIndex = 0;
static u16 mpHostCurrentChunkSize = 0;
static bool mpHostWaitingChunkAck = false;
static bool mpHostTransferReady = false;
static bool mpHostTransferFailed = false;
static int mpHostChunkSendCounter = 0;
static MpRomChunkPacket mpHostCurrentChunk = {};

static const char mpClientTempRomPath[] =
    "sdmc:/virtuanes_localplay_session.nes";

static FILE *mpClientTransferFile = NULL;
static u32 mpClientExpectedRomSize = 0;
static u32 mpClientExpectedRomCrc32 = 0;
static u32 mpClientReceivedSize = 0;
static u32 mpClientExpectedChunk = 0;
static u32 mpClientCrcState = 0xFFFFFFFF;
static bool mpClientTransferReady = false;
static bool mpClientTransferFailed = false;
static int mpClientReadySendCounter = 0;


enum MpHostStartState
{
    MP_HOST_START_IDLE = 0,
    MP_HOST_START_REQUESTING,
    MP_HOST_START_GUEST_READY,
    MP_HOST_START_GO,
    MP_HOST_START_DONE
};

static MpHostStartState mpHostStartState =
    MP_HOST_START_IDLE;

static u32 mpHostStartToken = 0;
static int mpHostStartSendCounter = 0;

static u32 mpClientStartToken = 0;
static bool mpClientPreparedForStart = false;

static bool mpHostStateManifestAcked = false;
static bool mpHostStateWaitingChunkAck = false;
static bool mpHostStateReady = false;
static bool mpHostStateFailed = false;

static u32 mpHostStateSize = 0;
static u32 mpHostStateCrc32 = 0;
static u32 mpHostStateOffset = 0;
static u32 mpHostStateChunkIndex = 0;

static u16 mpHostStateCurrentChunkSize = 0;

static int mpHostStateManifestSendCounter = 0;
static int mpHostStateChunkSendCounter = 0;

static FILE *mpHostStateFile = NULL;

static MpStateChunkPacket mpHostStateCurrentChunk = {};


static bool mpClientStateManifestReceived = false;
static bool mpClientStateReady = false;
static bool mpClientStateFailed = false;

static u32 mpClientExpectedStateSize = 0;
static u32 mpClientExpectedStateCrc32 = 0;
static u32 mpClientStateReceivedSize = 0;
static u32 mpClientStateExpectedChunk = 0;
static u32 mpClientStateCrcState = 0xFFFFFFFF;

static int mpClientStateReadySendCounter = 0;

static FILE *mpClientStateFile = NULL;


static u8 mpLatestP2Buttons = 0;

static u16 mpLatestSyncInput = 0;
static bool mpHaveSyncInput = false;

static u32 mpClientInputSequence = 0;
static u32 mpHostInputSequence = 0;

static u32 mpLockstepFrame = 0;
static bool mpLockstepInitialized = false;

static bool mpHostHavePreviousSync = false;
static MpSyncInputPacket mpHostPreviousSync = {};


// P2 transport state.
static u8 mpLastSentP2Buttons = 0xFF;
static int mpP2HeartbeatFrames = 0;

static bool mpHaveP2Sequence = false;
static u32 mpLastP2Sequence = 0;
static int mpP2FramesSincePacket = 0;


static u32 mpCrc32Update(u32 crc, const u8 *data, size_t size)
{
    for (size_t i = 0; i < size; i++)
    {
        crc ^= data[i];

        for (int bit = 0; bit < 8; bit++)
        {
            if (crc & 1)
                crc = (crc >> 1) ^ 0xEDB88320;
            else
                crc >>= 1;
        }
    }

    return crc;
}


static bool mpCalculateFileCrc32(const char *path, u32 *output)
{
    FILE *file = fopen(path, "rb");

    if (!file)
        return false;

    u8 buffer[4096];
    u32 crc = 0xFFFFFFFF;

    while (true)
    {
        size_t count = fread(buffer, 1, sizeof(buffer), file);

        if (count > 0)
            crc = mpCrc32Update(crc, buffer, count);

        if (count < sizeof(buffer))
        {
            if (ferror(file))
            {
                fclose(file);
                return false;
            }

            break;
        }
    }

    fclose(file);

    *output = crc ^ 0xFFFFFFFF;
    return true;
}


static void mpResetHostTransfer()
{
    if (mpHostTransferFile)
    {
        fclose(mpHostTransferFile);
        mpHostTransferFile = NULL;
    }

    mpManifestAcked = false;
    mpManifestSendCounter = 10;

    mpHostTransferOffset = 0;
    mpHostChunkIndex = 0;
    mpHostCurrentChunkSize = 0;
    mpHostWaitingChunkAck = false;
    mpHostTransferReady = false;
    mpHostTransferFailed = false;
    mpHostChunkSendCounter = 0;

    mpHostStartState = MP_HOST_START_IDLE;
    mpHostStartToken = 0;
    mpHostStartSendCounter = 0;

    memset(&mpHostCurrentChunk, 0, sizeof(mpHostCurrentChunk));
}


static void mpResetClientTransfer(bool deleteTempFile)
{
    if (mpClientTransferFile)
    {
        fclose(mpClientTransferFile);
        mpClientTransferFile = NULL;
    }

    mpClientManifestReceived = false;
    mpClientExpectedRomSize = 0;
    mpClientExpectedRomCrc32 = 0;
    mpClientReceivedSize = 0;
    mpClientExpectedChunk = 0;
    mpClientCrcState = 0xFFFFFFFF;
    mpClientTransferReady = false;
    mpClientTransferFailed = false;
    mpClientReadySendCounter = 0;

    mpClientStartToken = 0;
    mpClientPreparedForStart = false;

    if (deleteTempFile)
        remove(mpClientTempRomPath);
}


static u8 mpMap3dsToNes(u32 keys)
{
    u8 nes = 0;

    if (keys & KEY_A)      nes |= BTNNES_A;
    if (keys & KEY_B)      nes |= BTNNES_B;
    if (keys & KEY_SELECT) nes |= BTNNES_SELECT;
    if (keys & KEY_START)  nes |= BTNNES_START;
    if (keys & KEY_DUP)    nes |= BTNNES_UP;
    if (keys & KEY_DDOWN)  nes |= BTNNES_DOWN;
    if (keys & KEY_DLEFT)  nes |= BTNNES_LEFT;
    if (keys & KEY_DRIGHT) nes |= BTNNES_RIGHT;

    return nes;
}


bool impl3dsLocalPlayStartHost(
    const char *gameName,
    const char *romPath)
{
    if (mpHostActive)
        return true;

    FILE *rom = fopen(romPath, "rb");

    if (!rom)
        return false;

    if (fseek(rom, 0, SEEK_END) != 0)
    {
        fclose(rom);
        return false;
    }

    long fileSize = ftell(rom);
    fclose(rom);

    if (fileSize < 0)
        return false;

    mpHostRomSize = (u32)fileSize;

    strncpy(
        mpHostRomPath,
        romPath,
        sizeof(mpHostRomPath) - 1
    );
    mpHostRomPath[sizeof(mpHostRomPath) - 1] = '\0';

    if (!mpCalculateFileCrc32(
            mpHostRomPath,
            &mpHostRomCrc32))
    {
        return false;
    }

    mpResetHostTransfer();

    strncpy(
        mpHostGameName,
        gameName ? gameName : "Unknown",
        sizeof(mpHostGameName) - 1
    );

    mpHostGameName[sizeof(mpHostGameName) - 1] = '\0';

    mpManifestAcked = false;

    // Cause the first poll to send immediately.
    mpManifestSendCounter = 10;

    Result ret = udsInit(0x3000, NULL);

    if (R_FAILED(ret))
        return false;

    mpUdsInitialized = true;

    udsNetworkStruct network;

    udsGenerateDefaultNetworkStruct(
        &network,
        MP_WLAN_COMM_ID,
        0,
        MP_MAX_NODES
    );

    ret = udsCreateNetwork(
        &network,
        mpPassphrase,
        strlen(mpPassphrase) + 1,
        &mpBindCtx,
        MP_DATA_CHANNEL,
        UDS_DEFAULT_RECVBUFSIZE
    );

    if (R_SUCCEEDED(ret))
    {
        MpLobbyAppData appData = {};

        memcpy(appData.magic, "VNMP", 4);
        appData.version = MP_LOBBY_VERSION;

        strncpy(
            appData.gameName,
            gameName ? gameName : "Unknown",
            sizeof(appData.gameName) - 1
        );

        ret = udsSetApplicationData(&appData, sizeof(appData));

        if (R_FAILED(ret))
        {
            udsDestroyNetwork();
            udsUnbind(&mpBindCtx);
            udsExit();

            mpUdsInitialized = false;
            mpHostActive = false;

            return false;
        }

        mpHostActive = true;
        mpRemoteKeys = 0;
        return true;
    }

    udsExit();
    mpUdsInitialized = false;
    return false;
}


int impl3dsLocalPlayScanHosts(
    char hostNames[][32],
    char gameNames[][96],
    int maxHosts)
{
    if (mpHostActive || mpClientActive)
        return 0;

    if (maxHosts > MP_MAX_DISCOVERED)
        maxHosts = MP_MAX_DISCOVERED;

    if (maxHosts <= 0)
        return 0;

    if (!mpUdsInitialized)
    {
        Result ret = udsInit(0x3000, NULL);

        if (R_FAILED(ret))
            return 0;

        mpUdsInitialized = true;
    }

    mpDiscoveredCount = 0;

    void *scanbuf = malloc(MP_SCAN_BUF_SIZE);

    if (!scanbuf)
    {
        udsExit();
        mpUdsInitialized = false;
        return 0;
    }

    for (int attempt = 0; attempt < 60; attempt++)
    {
        udsNetworkScanInfo *networks = NULL;
        size_t totalNetworks = 0;

        Result ret = udsScanBeacons(
            scanbuf,
            MP_SCAN_BUF_SIZE,
            &networks,
            &totalNetworks,
            MP_WLAN_COMM_ID,
            0,
            NULL,
            false
        );

        if (R_FAILED(ret))
        {
            free(networks);
            free(scanbuf);

            udsExit();
            mpUdsInitialized = false;

            return 0;
        }

        for (size_t i = 0;
             i < totalNetworks && mpDiscoveredCount < maxHosts;
             i++)
        {
            MpLobbyAppData appData = {};
            size_t actualSize = 0;

            Result appRet = udsGetNetworkStructApplicationData(
                &networks[i].network,
                &appData,
                sizeof(appData),
                &actualSize
            );

            // Only show VirtuaNES multiplayer lobbies
            // using our current protocol version.
            if (R_FAILED(appRet) ||
                actualSize < 5 ||
                memcmp(appData.magic, "VNMP", 4) != 0 ||
                appData.version != MP_LOBBY_VERSION)
            {
                continue;
            }

            int n = mpDiscoveredCount;

            mpDiscoveredNetworks[n] = networks[i].network;

            strncpy(hostNames[n], "Host", 31);
            hostNames[n][31] = '\0';

            appData.gameName[sizeof(appData.gameName) - 1] = '\0';

            strncpy(gameNames[n], appData.gameName, 95);
            gameNames[n][95] = '\0';

            // Find the host's 3DS username.
            for (int node = 0; node < UDS_MAXNODES; node++)
            {
                if (!udsCheckNodeInfoInitialized(
                        &networks[i].nodes[node]))
                {
                    continue;
                }

                if (networks[i].nodes[node].NetworkNodeID ==
                    UDS_HOST_NETWORKNODEID)
                {
                    char username[32] = {};

                    if (R_SUCCEEDED(
                            udsGetNodeInfoUsername(
                                &networks[i].nodes[node],
                                username)))
                    {
                        strncpy(hostNames[n], username, 31);
                        hostNames[n][31] = '\0';
                    }

                    break;
                }
            }

            mpDiscoveredCount++;
        }

        free(networks);

        if (mpDiscoveredCount > 0)
            break;

        gspWaitForVBlank();
    }

    free(scanbuf);

    if (mpDiscoveredCount == 0)
    {
        udsExit();
        mpUdsInitialized = false;
    }

    return mpDiscoveredCount;
}


bool impl3dsLocalPlayJoinScannedHost(int index)
{
    if (!mpUdsInitialized)
        return false;

    if (mpClientActive || mpHostActive)
        return false;

    if (index < 0 || index >= mpDiscoveredCount)
        return false;

    Result ret = udsConnectNetwork(
        &mpDiscoveredNetworks[index],
        mpPassphrase,
        strlen(mpPassphrase) + 1,
        &mpBindCtx,
        UDS_BROADCAST_NETWORKNODEID,
        UDSCONTYPE_Client,
        MP_DATA_CHANNEL,
        UDS_DEFAULT_RECVBUFSIZE
    );

    if (R_FAILED(ret))
        return false;

    mpClientActive = true;
    mpRemoteKeys = 0;

    return true;
}


bool impl3dsLocalPlayJoinFirstHost(
    char *hostName,
    size_t hostNameSize,
    char *gameName,
    size_t gameNameSize)
{
    if (mpClientActive)
        return true;

    if (mpHostActive)
        return false;

    Result ret = udsInit(0x3000, NULL);

    if (R_FAILED(ret))
        return false;

    mpUdsInitialized = true;

    void *scanbuf = malloc(MP_SCAN_BUF_SIZE);

    if (!scanbuf)
    {
        udsExit();
        mpUdsInitialized = false;
        return false;
    }

    for (int attempt = 0; attempt < 60; attempt++)
    {
        udsNetworkScanInfo *networks = NULL;
        size_t totalNetworks = 0;

        ret = udsScanBeacons(
            scanbuf,
            MP_SCAN_BUF_SIZE,
            &networks,
            &totalNetworks,
            MP_WLAN_COMM_ID,
            0,
            NULL,
            false
        );

        if (R_FAILED(ret))
        {
            free(networks);
            free(scanbuf);
            udsExit();
            mpUdsInitialized = false;
            return false;
        }

        if (totalNetworks > 0)
        {
            char scannedHost[32] = "Host";
            char scannedGame[MP_GAME_NAME_MAX] = "Unknown";

            // Read the host's 3DS username from the scan result.
            for (int i = 0; i < UDS_MAXNODES; i++)
            {
                if (!udsCheckNodeInfoInitialized(&networks[0].nodes[i]))
                    continue;

                if (networks[0].nodes[i].NetworkNodeID ==
                    UDS_HOST_NETWORKNODEID)
                {
                    udsGetNodeInfoUsername(
                        &networks[0].nodes[i],
                        scannedHost
                    );
                    break;
                }
            }

            // Read VirtuaNES lobby metadata from the beacon.
            MpLobbyAppData appData = {};
            size_t actualSize = 0;

            Result appRet = udsGetNetworkStructApplicationData(
                &networks[0].network,
                &appData,
                sizeof(appData),
                &actualSize
            );

            if (R_SUCCEEDED(appRet) &&
                actualSize >= 5 &&
                memcmp(appData.magic, "VNMP", 4) == 0 &&
                appData.version == MP_LOBBY_VERSION)
            {
                appData.gameName[sizeof(appData.gameName) - 1] = '\0';

                strncpy(
                    scannedGame,
                    appData.gameName,
                    sizeof(scannedGame) - 1
                );

                scannedGame[sizeof(scannedGame) - 1] = '\0';
            }

            ret = udsConnectNetwork(
                &networks[0].network,
                mpPassphrase,
                strlen(mpPassphrase) + 1,
                &mpBindCtx,
                UDS_BROADCAST_NETWORKNODEID,
                UDSCONTYPE_Client,
                MP_DATA_CHANNEL,
                UDS_DEFAULT_RECVBUFSIZE
            );

            free(networks);
            free(scanbuf);

            if (R_SUCCEEDED(ret))
            {
                mpClientActive = true;
                mpRemoteKeys = 0;

                if (hostName && hostNameSize)
                {
                    strncpy(hostName, scannedHost, hostNameSize - 1);
                    hostName[hostNameSize - 1] = '\0';
                }

                if (gameName && gameNameSize)
                {
                    strncpy(gameName, scannedGame, gameNameSize - 1);
                    gameName[gameNameSize - 1] = '\0';
                }

                return true;
            }

            udsExit();
            mpUdsInitialized = false;
            return false;
        }

        free(networks);
        gspWaitForVBlank();
    }

    free(scanbuf);

    udsExit();
    mpUdsInitialized = false;

    return false;
}


bool impl3dsLocalPlayClientHasHost()
{
    if (!mpClientActive)
        return false;

    udsConnectionStatus status;

    Result ret = udsGetConnectionStatus(&status);

    if (R_FAILED(ret))
        return false;

    // NetworkNodeID 1 is always the host.
    return (status.node_bitmask & BIT(0)) != 0 &&
           status.total_nodes >= 2;
}


bool impl3dsLocalPlayHostPollTransfer(
    u32 *sentBytes,
    u32 *totalBytes,
    bool *ready,
    bool *failed)
{
    bool changed = false;

    if (sentBytes)
        *sentBytes = mpHostTransferOffset;

    if (totalBytes)
        *totalBytes = mpHostRomSize;

    if (ready)
        *ready = mpHostTransferReady;

    if (failed)
        *failed = mpHostTransferFailed;

    if (!mpHostActive)
        return false;

    udsConnectionStatus status;

    if (R_FAILED(udsGetConnectionStatus(&status)) ||
        status.total_nodes < 2)
    {
        if (mpManifestAcked ||
            mpHostTransferOffset ||
            mpHostWaitingChunkAck ||
            mpHostTransferReady ||
            mpHostTransferFailed)
        {
            mpResetHostTransfer();
            changed = true;
        }

        return changed;
    }

    if (mpHostTransferReady || mpHostTransferFailed)
    {
        if (sentBytes)
            *sentBytes = mpHostTransferOffset;

        if (totalBytes)
            *totalBytes = mpHostRomSize;

        if (ready)
            *ready = mpHostTransferReady;

        if (failed)
            *failed = mpHostTransferFailed;

        return changed;
    }

    // -----------------------------------------------------
    // Process one incoming control packet.
    // -----------------------------------------------------

    MpRomChunkPacket incoming = {};
    size_t receivedSize = 0;
    u16 sourceNode = 0;

    Result ret = udsPullPacket(
        &mpBindCtx,
        &incoming,
        sizeof(incoming),
        &receivedSize,
        &sourceNode
    );

    if (R_SUCCEEDED(ret) &&
        receivedSize >= sizeof(MpPacketHeader))
    {
        MpPacketHeader *header =
            (MpPacketHeader *)&incoming;

        if (memcmp(header->magic, "VNMP", 4) == 0 &&
            header->version == MP_LOBBY_VERSION)
        {
            if (header->type == MP_PACKET_MANIFEST_ACK &&
                receivedSize == sizeof(MpManifestAckPacket))
            {
                if (!mpManifestAcked)
                {
                    mpManifestAcked = true;
                    changed = true;
                }
            }
            else if (
                header->type == MP_PACKET_ROM_CHUNK_ACK &&
                receivedSize == sizeof(MpRomChunkAckPacket))
            {
                MpRomChunkAckPacket *ack =
                    (MpRomChunkAckPacket *)&incoming;

                if (mpHostWaitingChunkAck &&
                    ack->chunkIndex == mpHostChunkIndex)
                {
                    mpHostTransferOffset +=
                        mpHostCurrentChunkSize;

                    mpHostChunkIndex++;
                    mpHostWaitingChunkAck = false;
                    mpHostChunkSendCounter = 0;

                    changed = true;
                }
            }
            else if (
                header->type == MP_PACKET_ROM_READY &&
                receivedSize == sizeof(MpRomReadyPacket))
            {
                MpRomReadyPacket *readyPacket =
                    (MpRomReadyPacket *)&incoming;

                if (readyPacket->romSize == mpHostRomSize &&
                    readyPacket->romCrc32 == mpHostRomCrc32)
                {
                    mpHostTransferReady = true;

                    if (mpHostTransferFile)
                    {
                        fclose(mpHostTransferFile);
                        mpHostTransferFile = NULL;
                    }

                    changed = true;
                }
            }
            else if (header->type == MP_PACKET_ROM_ERROR)
            {
                mpHostTransferFailed = true;

                if (mpHostTransferFile)
                {
                    fclose(mpHostTransferFile);
                    mpHostTransferFile = NULL;
                }

                changed = true;
            }
        }
    }

    if (mpHostTransferReady || mpHostTransferFailed)
    {
        if (sentBytes)
            *sentBytes = mpHostTransferOffset;

        if (ready)
            *ready = mpHostTransferReady;

        if (failed)
            *failed = mpHostTransferFailed;

        return changed;
    }

    // -----------------------------------------------------
    // Manifest handshake.
    // -----------------------------------------------------

    if (!mpManifestAcked)
    {
        mpManifestSendCounter++;

        if (mpManifestSendCounter >= 10)
        {
            mpManifestSendCounter = 0;

            MpManifestPacket packet = {};

            memcpy(packet.header.magic, "VNMP", 4);
            packet.header.version = MP_LOBBY_VERSION;
            packet.header.type = MP_PACKET_MANIFEST;
            packet.header.payloadSize =
                sizeof(packet) - sizeof(packet.header);

            packet.romSize = mpHostRomSize;
            packet.romCrc32 = mpHostRomCrc32;

            strncpy(
                packet.gameName,
                mpHostGameName,
                sizeof(packet.gameName) - 1
            );

            udsSendTo(
                UDS_BROADCAST_NETWORKNODEID,
                MP_DATA_CHANNEL,
                UDS_SENDFLAG_Default,
                &packet,
                sizeof(packet)
            );
        }

        return changed;
    }

    // -----------------------------------------------------
    // Open ROM when the guest accepted the manifest.
    // -----------------------------------------------------

    if (!mpHostTransferFile &&
        mpHostTransferOffset < mpHostRomSize)
    {
        mpHostTransferFile =
            fopen(mpHostRomPath, "rb");

        if (!mpHostTransferFile)
        {
            mpHostTransferFailed = true;

            if (failed)
                *failed = true;

            return true;
        }
    }

    // -----------------------------------------------------
    // Build a new chunk if the previous one was ACKed.
    // -----------------------------------------------------

    if (!mpHostWaitingChunkAck &&
        mpHostTransferOffset < mpHostRomSize)
    {
        memset(
            &mpHostCurrentChunk,
            0,
            sizeof(mpHostCurrentChunk)
        );

        memcpy(
            mpHostCurrentChunk.header.magic,
            "VNMP",
            4
        );

        mpHostCurrentChunk.header.version =
            MP_LOBBY_VERSION;

        mpHostCurrentChunk.header.type =
            MP_PACKET_ROM_CHUNK;

        mpHostCurrentChunk.chunkIndex =
            mpHostChunkIndex;

        mpHostCurrentChunk.offset =
            mpHostTransferOffset;

        size_t count = fread(
            mpHostCurrentChunk.data,
            1,
            MP_ROM_CHUNK_SIZE,
            mpHostTransferFile
        );

        if (count == 0)
        {
            mpHostTransferFailed = true;

            if (failed)
                *failed = true;

            return true;
        }

        mpHostCurrentChunk.dataSize = (u16)count;
        mpHostCurrentChunkSize = (u16)count;

        mpHostCurrentChunk.header.payloadSize =
            sizeof(mpHostCurrentChunk) -
            sizeof(mpHostCurrentChunk.header);

        mpHostWaitingChunkAck = true;

        // Send immediately.
        mpHostChunkSendCounter = 10;
    }

    // -----------------------------------------------------
    // Send/re-send current chunk until acknowledged.
    // -----------------------------------------------------

    if (mpHostWaitingChunkAck)
    {
        mpHostChunkSendCounter++;

        if (mpHostChunkSendCounter >= 10)
        {
            mpHostChunkSendCounter = 0;

            Result sendRet = udsSendTo(
                UDS_BROADCAST_NETWORKNODEID,
                MP_DATA_CHANNEL,
                UDS_SENDFLAG_Default,
                &mpHostCurrentChunk,
                sizeof(mpHostCurrentChunk)
            );

            if (UDS_CHECK_SENDTO_FATALERROR(sendRet))
            {
                mpHostTransferFailed = true;

                if (failed)
                    *failed = true;

                return true;
            }
        }
    }

    if (sentBytes)
        *sentBytes = mpHostTransferOffset;

    if (totalBytes)
        *totalBytes = mpHostRomSize;

    if (ready)
        *ready = mpHostTransferReady;

    if (failed)
        *failed = mpHostTransferFailed;

    return changed;
}


bool impl3dsLocalPlayClientPollTransfer(
    char *gameName,
    size_t gameNameSize,
    u32 *receivedBytes,
    u32 *totalBytes,
    bool *ready,
    bool *failed)
{
    bool changed = false;

    if (receivedBytes)
        *receivedBytes = mpClientReceivedSize;

    if (totalBytes)
        *totalBytes = mpClientExpectedRomSize;

    if (ready)
        *ready = mpClientTransferReady;

    if (failed)
        *failed = mpClientTransferFailed;

    if (!mpClientActive)
        return false;

    // Once complete, periodically re-send READY in case
    // the previous packet was lost.
    if (mpClientTransferReady)
    {
        mpClientReadySendCounter++;

        if (mpClientReadySendCounter >= 30)
        {
            mpClientReadySendCounter = 0;

            MpRomReadyPacket readyPacket = {};

            memcpy(
                readyPacket.header.magic,
                "VNMP",
                4
            );

            readyPacket.header.version =
                MP_LOBBY_VERSION;

            readyPacket.header.type =
                MP_PACKET_ROM_READY;

            readyPacket.header.payloadSize =
                sizeof(readyPacket) -
                sizeof(readyPacket.header);

            readyPacket.romSize =
                mpClientExpectedRomSize;

            readyPacket.romCrc32 =
                mpClientExpectedRomCrc32;

            udsSendTo(
                UDS_HOST_NETWORKNODEID,
                MP_DATA_CHANNEL,
                UDS_SENDFLAG_Default,
                &readyPacket,
                sizeof(readyPacket)
            );
        }

        return false;
    }

    MpRomChunkPacket incoming = {};
    size_t receivedSize = 0;
    u16 sourceNode = 0;

    Result ret = udsPullPacket(
        &mpBindCtx,
        &incoming,
        sizeof(incoming),
        &receivedSize,
        &sourceNode
    );

    if (R_FAILED(ret) || receivedSize == 0)
        return false;

    if (receivedSize < sizeof(MpPacketHeader))
        return false;

    MpPacketHeader *header =
        (MpPacketHeader *)&incoming;

    if (memcmp(header->magic, "VNMP", 4) != 0 ||
        header->version != MP_LOBBY_VERSION)
    {
        return false;
    }

    // -----------------------------------------------------
    // MANIFEST
    // -----------------------------------------------------

    if (header->type == MP_PACKET_MANIFEST &&
        receivedSize == sizeof(MpManifestPacket))
    {
        MpManifestPacket *manifest =
            (MpManifestPacket *)&incoming;

        manifest->gameName[
            sizeof(manifest->gameName) - 1
        ] = '\0';

        if (!mpClientManifestReceived)
        {
            mpResetClientTransfer(true);

            mpClientExpectedRomSize =
                manifest->romSize;

            mpClientExpectedRomCrc32 =
                manifest->romCrc32;

            mpClientCrcState = 0xFFFFFFFF;

            mpClientTransferFile =
                fopen(mpClientTempRomPath, "wb");

            if (!mpClientTransferFile)
            {
                mpClientTransferFailed = true;

                MpRomErrorPacket error = {};

                memcpy(error.header.magic, "VNMP", 4);
                error.header.version = MP_LOBBY_VERSION;
                error.header.type = MP_PACKET_ROM_ERROR;

                udsSendTo(
                    UDS_HOST_NETWORKNODEID,
                    MP_DATA_CHANNEL,
                    UDS_SENDFLAG_Default,
                    &error,
                    sizeof(error)
                );

                if (failed)
                    *failed = true;

                return true;
            }

            mpClientManifestReceived = true;

            if (gameName && gameNameSize)
            {
                strncpy(
                    gameName,
                    manifest->gameName,
                    gameNameSize - 1
                );

                gameName[gameNameSize - 1] = '\0';
            }

            changed = true;
        }

        // ACK every repeated manifest too.
        MpManifestAckPacket ack = {};

        memcpy(ack.header.magic, "VNMP", 4);
        ack.header.version = MP_LOBBY_VERSION;
        ack.header.type = MP_PACKET_MANIFEST_ACK;

        udsSendTo(
            UDS_HOST_NETWORKNODEID,
            MP_DATA_CHANNEL,
            UDS_SENDFLAG_Default,
            &ack,
            sizeof(ack)
        );
    }

    // -----------------------------------------------------
    // ROM CHUNK
    // -----------------------------------------------------

    else if (
        header->type == MP_PACKET_ROM_CHUNK &&
        receivedSize == sizeof(MpRomChunkPacket) &&
        mpClientManifestReceived &&
        !mpClientTransferFailed)
    {
        MpRomChunkPacket *chunk =
            (MpRomChunkPacket *)&incoming;

        if (chunk->dataSize > MP_ROM_CHUNK_SIZE)
            return false;

        // Duplicate chunk: our previous ACK was probably
        // lost. ACK it again, but do not write twice.
        if (chunk->chunkIndex < mpClientExpectedChunk)
        {
            MpRomChunkAckPacket ack = {};

            memcpy(ack.header.magic, "VNMP", 4);
            ack.header.version = MP_LOBBY_VERSION;
            ack.header.type = MP_PACKET_ROM_CHUNK_ACK;
            ack.chunkIndex = chunk->chunkIndex;

            udsSendTo(
                UDS_HOST_NETWORKNODEID,
                MP_DATA_CHANNEL,
                UDS_SENDFLAG_Default,
                &ack,
                sizeof(ack)
            );

            return false;
        }

        if (chunk->chunkIndex != mpClientExpectedChunk ||
            chunk->offset != mpClientReceivedSize)
        {
            return false;
        }

        if (mpClientReceivedSize + chunk->dataSize >
            mpClientExpectedRomSize)
        {
            mpClientTransferFailed = true;
        }
        else
        {
            size_t written = fwrite(
                chunk->data,
                1,
                chunk->dataSize,
                mpClientTransferFile
            );

            if (written != chunk->dataSize)
            {
                mpClientTransferFailed = true;
            }
            else
            {
                mpClientCrcState = mpCrc32Update(
                    mpClientCrcState,
                    chunk->data,
                    chunk->dataSize
                );

                mpClientReceivedSize +=
                    chunk->dataSize;

                mpClientExpectedChunk++;

                changed = true;

                MpRomChunkAckPacket ack = {};

                memcpy(ack.header.magic, "VNMP", 4);
                ack.header.version =
                    MP_LOBBY_VERSION;
                ack.header.type =
                    MP_PACKET_ROM_CHUNK_ACK;
                ack.chunkIndex =
                    chunk->chunkIndex;

                udsSendTo(
                    UDS_HOST_NETWORKNODEID,
                    MP_DATA_CHANNEL,
                    UDS_SENDFLAG_Default,
                    &ack,
                    sizeof(ack)
                );
            }
        }

        if (mpClientTransferFailed)
        {
            if (mpClientTransferFile)
            {
                fclose(mpClientTransferFile);
                mpClientTransferFile = NULL;
            }

            remove(mpClientTempRomPath);

            MpRomErrorPacket error = {};

            memcpy(error.header.magic, "VNMP", 4);
            error.header.version = MP_LOBBY_VERSION;
            error.header.type = MP_PACKET_ROM_ERROR;

            udsSendTo(
                UDS_HOST_NETWORKNODEID,
                MP_DATA_CHANNEL,
                UDS_SENDFLAG_Default,
                &error,
                sizeof(error)
            );

            changed = true;
        }

        // -------------------------------------------------
        // Complete ROM received: close + verify CRC32.
        // -------------------------------------------------

        if (!mpClientTransferFailed &&
            mpClientReceivedSize ==
                mpClientExpectedRomSize)
        {
            fflush(mpClientTransferFile);
            fclose(mpClientTransferFile);
            mpClientTransferFile = NULL;

            u32 finalCrc =
                mpClientCrcState ^ 0xFFFFFFFF;

            if (finalCrc ==
                mpClientExpectedRomCrc32)
            {
                mpClientTransferReady = true;
                mpClientReadySendCounter = 30;

                changed = true;
            }
            else
            {
                mpClientTransferFailed = true;
                remove(mpClientTempRomPath);

                MpRomErrorPacket error = {};

                memcpy(
                    error.header.magic,
                    "VNMP",
                    4
                );

                error.header.version =
                    MP_LOBBY_VERSION;

                error.header.type =
                    MP_PACKET_ROM_ERROR;

                udsSendTo(
                    UDS_HOST_NETWORKNODEID,
                    MP_DATA_CHANNEL,
                    UDS_SENDFLAG_Default,
                    &error,
                    sizeof(error)
                );

                changed = true;
            }
        }
    }

    if (receivedBytes)
        *receivedBytes = mpClientReceivedSize;

    if (totalBytes)
        *totalBytes = mpClientExpectedRomSize;

    if (ready)
        *ready = mpClientTransferReady;

    if (failed)
        *failed = mpClientTransferFailed;

    return changed;
}


static bool mpGetFileSizeAndCrc32(
    const char *path,
    u32 *sizeOut,
    u32 *crcOut)
{
    FILE *fp = fopen(path, "rb");

    if (!fp)
        return false;

    u8 buffer[4096];
    u64 total = 0;
    u32 crc = 0xFFFFFFFF;

    while (true)
    {
        size_t count = fread(
            buffer,
            1,
            sizeof(buffer),
            fp
        );

        if (count > 0)
        {
            total += count;

            if (total > 0xFFFFFFFFULL)
            {
                fclose(fp);
                return false;
            }

            crc = mpCrc32Update(
                crc,
                buffer,
                count
            );
        }

        if (count < sizeof(buffer))
        {
            if (ferror(fp))
            {
                fclose(fp);
                return false;
            }

            break;
        }
    }

    fclose(fp);

    if (total == 0)
        return false;

    if (sizeOut)
        *sizeOut = (u32)total;

    if (crcOut)
        *crcOut = crc ^ 0xFFFFFFFF;

    return true;
}


static void mpSendStateManifestAck(u32 token)
{
    MpStateManifestAckPacket packet = {};

    memcpy(packet.header.magic, "VNMP", 4);
    packet.header.version = MP_LOBBY_VERSION;
    packet.header.type = MP_PACKET_STATE_MANIFEST_ACK;
    packet.header.payloadSize =
        sizeof(packet) - sizeof(packet.header);

    packet.token = token;

    udsSendTo(
        UDS_HOST_NETWORKNODEID,
        MP_DATA_CHANNEL,
        UDS_SENDFLAG_Default,
        &packet,
        sizeof(packet)
    );
}


static void mpSendStateChunkAck(
    u32 token,
    u32 chunkIndex)
{
    MpStateChunkAckPacket packet = {};

    memcpy(packet.header.magic, "VNMP", 4);
    packet.header.version = MP_LOBBY_VERSION;
    packet.header.type = MP_PACKET_STATE_CHUNK_ACK;
    packet.header.payloadSize =
        sizeof(packet) - sizeof(packet.header);

    packet.token = token;
    packet.chunkIndex = chunkIndex;

    udsSendTo(
        UDS_HOST_NETWORKNODEID,
        MP_DATA_CHANNEL,
        UDS_SENDFLAG_Default,
        &packet,
        sizeof(packet)
    );
}


static void mpSendStateReady()
{
    if (!mpClientStateReady ||
        mpClientStartToken == 0)
    {
        return;
    }

    MpStateReadyPacket packet = {};

    memcpy(packet.header.magic, "VNMP", 4);
    packet.header.version = MP_LOBBY_VERSION;
    packet.header.type = MP_PACKET_STATE_READY;
    packet.header.payloadSize =
        sizeof(packet) - sizeof(packet.header);

    packet.token = mpClientStartToken;
    packet.stateSize = mpClientExpectedStateSize;
    packet.stateCrc32 = mpClientExpectedStateCrc32;

    udsSendTo(
        UDS_HOST_NETWORKNODEID,
        MP_DATA_CHANNEL,
        UDS_SENDFLAG_Default,
        &packet,
        sizeof(packet)
    );
}


static void mpSendStateError(u32 token)
{
    MpStateErrorPacket packet = {};

    memcpy(packet.header.magic, "VNMP", 4);
    packet.header.version = MP_LOBBY_VERSION;
    packet.header.type = MP_PACKET_STATE_ERROR;
    packet.header.payloadSize =
        sizeof(packet) - sizeof(packet.header);

    packet.token = token;

    udsSendTo(
        UDS_HOST_NETWORKNODEID,
        MP_DATA_CHANNEL,
        UDS_SENDFLAG_Default,
        &packet,
        sizeof(packet)
    );
}


// Forward declarations used by the Local Play start protocol.
static void mpResetHostStateTransfer(bool deleteFile);
static void mpResetClientStateTransfer(bool deleteFile);
extern NES* nes;


bool impl3dsLocalPlayHostBeginStart()
{
    if (!mpHostActive ||
        !mpHostTransferReady ||
        mpHostStartState != MP_HOST_START_IDLE)
    {
        return false;
    }

    mpResetHostStateTransfer(true);

    // Build the one canonical emulator instance that both
    // systems will start from.
    //
    // This intentionally loads the host's real ROM path,
    // including its normal SRAM/config behaviour.
    if (!impl3dsLoadROM(mpHostRomPath))
    {
        mpHostStateFailed = true;
        return false;
    }

    if (!nes ||
        !nes->SaveState(MP_HOST_STATE_PATH))
    {
        mpHostStateFailed = true;
        return false;
    }

    if (!mpGetFileSizeAndCrc32(
            MP_HOST_STATE_PATH,
            &mpHostStateSize,
            &mpHostStateCrc32))
    {
        mpHostStateFailed = true;
        return false;
    }

    mpHostStartToken =
        (u32)svcGetSystemTick();

    if (mpHostStartToken == 0)
        mpHostStartToken = 1;

    mpHostStartState =
        MP_HOST_START_REQUESTING;

    // Start manifest immediately.
    mpHostStateManifestSendCounter = 10;

    // A new multiplayer timeline begins only after GO.
    mpLockstepFrame = 0;
    mpLockstepInitialized = false;
    mpHostHavePreviousSync = false;
    memset(
        &mpHostPreviousSync,
        0,
        sizeof(mpHostPreviousSync)
    );

    return true;
}


int impl3dsLocalPlayHostPollStart()
{
    if (!mpHostActive ||
        mpHostStartState == MP_HOST_START_IDLE)
    {
        return 0;
    }

    // -----------------------------------------------------
    // Drain incoming state-control / GO packets.
    // -----------------------------------------------------

    for (int i = 0; i < 8; i++)
    {
        u8 buffer[UDS_DATAFRAME_MAXSIZE] = {};
        size_t receivedSize = 0;
        u16 sourceNode = 0;

        Result ret = udsPullPacket(
            &mpBindCtx,
            buffer,
            sizeof(buffer),
            &receivedSize,
            &sourceNode
        );

        if (R_FAILED(ret) || receivedSize == 0)
            break;

        if (receivedSize < sizeof(MpPacketHeader))
            continue;

        MpPacketHeader *header =
            (MpPacketHeader *)buffer;

        if (memcmp(header->magic, "VNMP", 4) != 0 ||
            header->version != MP_LOBBY_VERSION)
        {
            continue;
        }

        // -------------------------------------------------
        // Guest accepted state manifest.
        // -------------------------------------------------

        if (header->type ==
                MP_PACKET_STATE_MANIFEST_ACK &&
            receivedSize ==
                sizeof(MpStateManifestAckPacket) &&
            mpHostStartState ==
                MP_HOST_START_REQUESTING)
        {
            MpStateManifestAckPacket *ack =
                (MpStateManifestAckPacket *)buffer;

            if (ack->token == mpHostStartToken)
                mpHostStateManifestAcked = true;

            continue;
        }

        // -------------------------------------------------
        // Guest ACKed current state chunk.
        // -------------------------------------------------

        if (header->type ==
                MP_PACKET_STATE_CHUNK_ACK &&
            receivedSize ==
                sizeof(MpStateChunkAckPacket) &&
            mpHostStartState ==
                MP_HOST_START_REQUESTING)
        {
            MpStateChunkAckPacket *ack =
                (MpStateChunkAckPacket *)buffer;

            if (ack->token == mpHostStartToken &&
                mpHostStateWaitingChunkAck &&
                ack->chunkIndex ==
                    mpHostStateChunkIndex)
            {
                mpHostStateOffset +=
                    mpHostStateCurrentChunkSize;

                mpHostStateChunkIndex++;

                mpHostStateWaitingChunkAck = false;
                mpHostStateChunkSendCounter = 0;
            }

            continue;
        }

        // -------------------------------------------------
        // Guest verified AND loaded the canonical state.
        // -------------------------------------------------

        if (header->type ==
                MP_PACKET_STATE_READY &&
            receivedSize ==
                sizeof(MpStateReadyPacket) &&
            mpHostStartState ==
                MP_HOST_START_REQUESTING)
        {
            MpStateReadyPacket *ready =
                (MpStateReadyPacket *)buffer;

            if (ready->token == mpHostStartToken &&
                ready->stateSize == mpHostStateSize &&
                ready->stateCrc32 == mpHostStateCrc32)
            {
                mpHostStateReady = true;

                if (mpHostStateFile)
                {
                    fclose(mpHostStateFile);
                    mpHostStateFile = NULL;
                }

                mpHostStartState =
                    MP_HOST_START_GUEST_READY;

                return 1;
            }

            continue;
        }

        if (header->type ==
                MP_PACKET_STATE_ERROR &&
            receivedSize ==
                sizeof(MpStateErrorPacket))
        {
            MpStateErrorPacket *error =
                (MpStateErrorPacket *)buffer;

            if (error->token == mpHostStartToken)
            {
                mpHostStateFailed = true;

                if (mpHostStateFile)
                {
                    fclose(mpHostStateFile);
                    mpHostStateFile = NULL;
                }

                mpHostStartState =
                    MP_HOST_START_IDLE;

                return -1;
            }

            continue;
        }

        // -------------------------------------------------
        // Final GO acknowledgement.
        // -------------------------------------------------

        if (header->type == MP_PACKET_GO_ACK &&
            receivedSize == sizeof(MpStartPacket) &&
            mpHostStartState == MP_HOST_START_GO)
        {
            MpStartPacket *packet =
                (MpStartPacket *)buffer;

            if (packet->token == mpHostStartToken)
            {
                mpHostStartState =
                    MP_HOST_START_DONE;

                return 2;
            }
        }

        // Old ROM_READY and other stale control packets
        // are intentionally drained/ignored here.
    }

    // -----------------------------------------------------
    // Canonical state transfer.
    // -----------------------------------------------------

    if (mpHostStartState ==
        MP_HOST_START_REQUESTING)
    {
        if (mpHostStateFailed)
        {
            mpHostStartState =
                MP_HOST_START_IDLE;

            return -1;
        }

        // ---------------------------------------------
        // State manifest.
        // ---------------------------------------------

        if (!mpHostStateManifestAcked)
        {
            mpHostStateManifestSendCounter++;

            if (mpHostStateManifestSendCounter >= 10)
            {
                mpHostStateManifestSendCounter = 0;

                MpStateManifestPacket packet = {};

                memcpy(
                    packet.header.magic,
                    "VNMP",
                    4
                );

                packet.header.version =
                    MP_LOBBY_VERSION;

                packet.header.type =
                    MP_PACKET_STATE_MANIFEST;

                packet.header.payloadSize =
                    sizeof(packet) -
                    sizeof(packet.header);

                packet.token =
                    mpHostStartToken;

                packet.stateSize =
                    mpHostStateSize;

                packet.stateCrc32 =
                    mpHostStateCrc32;

                udsSendTo(
                    UDS_BROADCAST_NETWORKNODEID,
                    MP_DATA_CHANNEL,
                    UDS_SENDFLAG_Default,
                    &packet,
                    sizeof(packet)
                );
            }

            return 0;
        }

        // ---------------------------------------------
        // Open canonical state after manifest ACK.
        // ---------------------------------------------

        if (!mpHostStateFile &&
            mpHostStateOffset < mpHostStateSize)
        {
            mpHostStateFile =
                fopen(MP_HOST_STATE_PATH, "rb");

            if (!mpHostStateFile)
            {
                mpHostStateFailed = true;
                mpHostStartState =
                    MP_HOST_START_IDLE;

                return -1;
            }
        }

        // ---------------------------------------------
        // Build next state chunk.
        // ---------------------------------------------

        if (!mpHostStateWaitingChunkAck &&
            mpHostStateOffset < mpHostStateSize)
        {
            memset(
                &mpHostStateCurrentChunk,
                0,
                sizeof(mpHostStateCurrentChunk)
            );

            memcpy(
                mpHostStateCurrentChunk.header.magic,
                "VNMP",
                4
            );

            mpHostStateCurrentChunk.header.version =
                MP_LOBBY_VERSION;

            mpHostStateCurrentChunk.header.type =
                MP_PACKET_STATE_CHUNK;

            mpHostStateCurrentChunk.header.payloadSize =
                sizeof(mpHostStateCurrentChunk) -
                sizeof(
                    mpHostStateCurrentChunk.header
                );

            mpHostStateCurrentChunk.token =
                mpHostStartToken;

            mpHostStateCurrentChunk.chunkIndex =
                mpHostStateChunkIndex;

            mpHostStateCurrentChunk.offset =
                mpHostStateOffset;

            size_t count = fread(
                mpHostStateCurrentChunk.data,
                1,
                MP_ROM_CHUNK_SIZE,
                mpHostStateFile
            );

            if (count == 0)
            {
                mpHostStateFailed = true;

                if (mpHostStateFile)
                {
                    fclose(mpHostStateFile);
                    mpHostStateFile = NULL;
                }

                mpHostStartState =
                    MP_HOST_START_IDLE;

                return -1;
            }

            mpHostStateCurrentChunk.dataSize =
                (u16)count;

            mpHostStateCurrentChunkSize =
                (u16)count;

            mpHostStateWaitingChunkAck = true;

            // Send quickly. Unlike the ROM transfer this
            // is already inside an explicit Start phase.
            mpHostStateChunkSendCounter = 2;
        }

        // ---------------------------------------------
        // Send/re-send state chunk until ACKed.
        // ---------------------------------------------

        if (mpHostStateWaitingChunkAck)
        {
            mpHostStateChunkSendCounter++;

            if (mpHostStateChunkSendCounter >= 2)
            {
                mpHostStateChunkSendCounter = 0;

                Result sendRet = udsSendTo(
                    UDS_BROADCAST_NETWORKNODEID,
                    MP_DATA_CHANNEL,
                    UDS_SENDFLAG_Default,
                    &mpHostStateCurrentChunk,
                    sizeof(mpHostStateCurrentChunk)
                );

                if (UDS_CHECK_SENDTO_FATALERROR(
                        sendRet))
                {
                    mpHostStateFailed = true;

                    if (mpHostStateFile)
                    {
                        fclose(mpHostStateFile);
                        mpHostStateFile = NULL;
                    }

                    mpHostStartState =
                        MP_HOST_START_IDLE;

                    return -1;
                }
            }
        }

        return 0;
    }

    // -----------------------------------------------------
    // GO stage.
    // -----------------------------------------------------

    if (mpHostStartState ==
        MP_HOST_START_GO)
    {
        mpHostStartSendCounter++;

        if (mpHostStartSendCounter >= 5)
        {
            mpHostStartSendCounter = 0;

            MpStartPacket packet = {};

            memcpy(packet.header.magic, "VNMP", 4);

            packet.header.version =
                MP_LOBBY_VERSION;

            packet.header.type =
                MP_PACKET_GO;

            packet.header.payloadSize =
                sizeof(packet) -
                sizeof(packet.header);

            packet.token =
                mpHostStartToken;

            udsSendTo(
                UDS_BROADCAST_NETWORKNODEID,
                MP_DATA_CHANNEL,
                UDS_SENDFLAG_Default,
                &packet,
                sizeof(packet)
            );
        }
    }

    return 0;
}


void impl3dsLocalPlayHostSendGo()
{
    if (mpHostStartState !=
        MP_HOST_START_GUEST_READY)
    {
        return;
    }

    // Both consoles must enter gameplay with lockstep frame
    // numbering starting from exactly zero.
    mpLockstepFrame = 0;
    mpLockstepInitialized = false;
    mpHostHavePreviousSync = false;

    memset(
        &mpHostPreviousSync,
        0,
        sizeof(mpHostPreviousSync)
    );

    mpHostStartState =
        MP_HOST_START_GO;

    // Force an immediate GO send.
    mpHostStartSendCounter = 5;
}


int impl3dsLocalPlayClientPollStart()
{
    if (!mpClientActive ||
        !mpClientTransferReady)
    {
        return 0;
    }

    // Once canonical state has loaded, periodically resend
    // STATE_READY in case the host missed it.
    if (mpClientStateReady)
    {
        mpClientStateReadySendCounter++;

        if (mpClientStateReadySendCounter >= 30)
        {
            mpClientStateReadySendCounter = 0;
            mpSendStateReady();
        }
    }

    for (int i = 0; i < 8; i++)
    {
        u8 buffer[UDS_DATAFRAME_MAXSIZE] = {};
        size_t receivedSize = 0;
        u16 sourceNode = 0;

        Result ret = udsPullPacket(
            &mpBindCtx,
            buffer,
            sizeof(buffer),
            &receivedSize,
            &sourceNode
        );

        if (R_FAILED(ret) || receivedSize == 0)
            break;

        if (receivedSize < sizeof(MpPacketHeader))
            continue;

        MpPacketHeader *header =
            (MpPacketHeader *)buffer;

        if (memcmp(header->magic, "VNMP", 4) != 0 ||
            header->version != MP_LOBBY_VERSION)
        {
            continue;
        }

        // -------------------------------------------------
        // STATE MANIFEST
        // -------------------------------------------------

        if (header->type ==
                MP_PACKET_STATE_MANIFEST &&
            receivedSize ==
                sizeof(MpStateManifestPacket))
        {
            MpStateManifestPacket *manifest =
                (MpStateManifestPacket *)buffer;

            if (!mpClientStateManifestReceived)
            {
                mpResetClientStateTransfer(true);

                mpClientStartToken =
                    manifest->token;

                mpClientExpectedStateSize =
                    manifest->stateSize;

                mpClientExpectedStateCrc32 =
                    manifest->stateCrc32;

                mpClientStateCrcState =
                    0xFFFFFFFF;

                if (mpClientExpectedStateSize == 0)
                {
                    mpClientStateFailed = true;
                    mpSendStateError(
                        mpClientStartToken
                    );

                    return -1;
                }

                mpClientStateFile =
                    fopen(
                        MP_CLIENT_STATE_PATH,
                        "wb"
                    );

                if (!mpClientStateFile)
                {
                    mpClientStateFailed = true;
                    mpSendStateError(
                        mpClientStartToken
                    );

                    return -1;
                }

                mpClientStateManifestReceived =
                    true;
            }

            if (manifest->token ==
                mpClientStartToken)
            {
                mpSendStateManifestAck(
                    mpClientStartToken
                );
            }

            continue;
        }

        // -------------------------------------------------
        // STATE CHUNK
        // -------------------------------------------------

        if (header->type ==
                MP_PACKET_STATE_CHUNK &&
            receivedSize ==
                sizeof(MpStateChunkPacket) &&
            mpClientStateManifestReceived &&
            !mpClientStateFailed)
        {
            MpStateChunkPacket *chunk =
                (MpStateChunkPacket *)buffer;

            if (chunk->token !=
                mpClientStartToken)
            {
                continue;
            }

            if (chunk->dataSize >
                MP_ROM_CHUNK_SIZE)
            {
                continue;
            }

            // Previous ACK was lost.
            if (chunk->chunkIndex <
                mpClientStateExpectedChunk)
            {
                mpSendStateChunkAck(
                    mpClientStartToken,
                    chunk->chunkIndex
                );

                continue;
            }

            if (chunk->chunkIndex !=
                    mpClientStateExpectedChunk ||
                chunk->offset !=
                    mpClientStateReceivedSize)
            {
                continue;
            }

            if (mpClientStateReceivedSize +
                    chunk->dataSize >
                mpClientExpectedStateSize)
            {
                mpClientStateFailed = true;
            }
            else
            {
                size_t written = fwrite(
                    chunk->data,
                    1,
                    chunk->dataSize,
                    mpClientStateFile
                );

                if (written != chunk->dataSize)
                {
                    mpClientStateFailed = true;
                }
                else
                {
                    mpClientStateCrcState =
                        mpCrc32Update(
                            mpClientStateCrcState,
                            chunk->data,
                            chunk->dataSize
                        );

                    mpClientStateReceivedSize +=
                        chunk->dataSize;

                    mpClientStateExpectedChunk++;

                    mpSendStateChunkAck(
                        mpClientStartToken,
                        chunk->chunkIndex
                    );
                }
            }

            if (mpClientStateFailed)
            {
                if (mpClientStateFile)
                {
                    fclose(mpClientStateFile);
                    mpClientStateFile = NULL;
                }

                remove(MP_CLIENT_STATE_PATH);

                mpSendStateError(
                    mpClientStartToken
                );

                return -1;
            }

            // ---------------------------------------------
            // Complete state file.
            // ---------------------------------------------

            if (mpClientStateReceivedSize ==
                mpClientExpectedStateSize)
            {
                fflush(mpClientStateFile);
                fclose(mpClientStateFile);
                mpClientStateFile = NULL;

                u32 finalCrc =
                    mpClientStateCrcState ^
                    0xFFFFFFFF;

                if (finalCrc !=
                    mpClientExpectedStateCrc32)
                {
                    mpClientStateFailed = true;

                    remove(
                        MP_CLIENT_STATE_PATH
                    );

                    mpSendStateError(
                        mpClientStartToken
                    );

                    return -1;
                }

                // Load the transferred ROM first so the
                // VirtuaNES state CRC/game checks have the
                // correct cartridge underneath them.
                if (!impl3dsLoadROM(
                        mpClientTempRomPath))
                {
                    mpClientStateFailed = true;

                    mpSendStateError(
                        mpClientStartToken
                    );

                    return -1;
                }

                // THIS is the important part:
                // B now becomes an exact clone of A's
                // canonical emulator state.
                if (!nes ||
                    !nes->LoadState(
                        MP_CLIENT_STATE_PATH))
                {
                    mpClientStateFailed = true;

                    mpSendStateError(
                        mpClientStartToken
                    );

                    return -1;
                }

                mpClientStateReady = true;

                // Force immediate STATE_READY.
                mpClientStateReadySendCounter = 30;
                mpSendStateReady();
                mpClientStateReadySendCounter = 0;

                return 1;
            }

            continue;
        }

        // -------------------------------------------------
        // GO
        // -------------------------------------------------

        if (header->type == MP_PACKET_GO &&
            receivedSize == sizeof(MpStartPacket) &&
            mpClientStateReady)
        {
            MpStartPacket *packet =
                (MpStartPacket *)buffer;

            if (packet->token !=
                mpClientStartToken)
            {
                continue;
            }

            MpStartPacket ack = {};

            memcpy(
                ack.header.magic,
                "VNMP",
                4
            );

            ack.header.version =
                MP_LOBBY_VERSION;

            ack.header.type =
                MP_PACKET_GO_ACK;

            ack.header.payloadSize =
                sizeof(ack) -
                sizeof(ack.header);

            ack.token =
                mpClientStartToken;

            // A few copies are cheap and make the final
            // transition much harder to lose.
            for (int n = 0; n < 3; n++)
            {
                udsSendTo(
                    UDS_HOST_NETWORKNODEID,
                    MP_DATA_CHANNEL,
                    UDS_SENDFLAG_Default,
                    &ack,
                    sizeof(ack)
                );
            }

            // Both systems begin lockstep from frame 0.
            mpLockstepFrame = 0;
            mpLockstepInitialized = false;
            mpHostHavePreviousSync = false;

            memset(
                &mpHostPreviousSync,
                0,
                sizeof(mpHostPreviousSync)
            );

            return 2;
        }

        // Old ROM_READY / START_REQUEST packets are ignored.
    }

    return 0;
}


void impl3dsLocalPlayClientMarkStartReady()
{
    if (!mpClientActive ||
        !mpClientTransferReady ||
        mpClientStartToken == 0)
    {
        return;
    }

    mpClientPreparedForStart = true;

    MpStartPacket ready = {};

    memcpy(ready.header.magic, "VNMP", 4);
    ready.header.version = MP_LOBBY_VERSION;
    ready.header.type = MP_PACKET_START_READY;
    ready.header.payloadSize =
        sizeof(ready) - sizeof(ready.header);
    ready.token = mpClientStartToken;

    udsSendTo(
        UDS_HOST_NETWORKNODEID,
        MP_DATA_CHANNEL,
        UDS_SENDFLAG_Default,
        &ready,
        sizeof(ready)
    );
}


const char *impl3dsLocalPlayGetReceivedRomPath()
{
    return mpClientTempRomPath;
}


bool impl3dsLocalPlayHasGuest()
{
    if (!mpHostActive)
        return false;

    udsConnectionStatus status;

    Result ret = udsGetConnectionStatus(&status);

    if (R_FAILED(ret))
        return false;

    return status.total_nodes >= 2;
}


static void mpResetHostStateTransfer(bool deleteFile)
{
    if (mpHostStateFile)
    {
        fclose(mpHostStateFile);
        mpHostStateFile = NULL;
    }

    if (deleteFile)
        remove(MP_HOST_STATE_PATH);

    mpHostStateManifestAcked = false;
    mpHostStateWaitingChunkAck = false;
    mpHostStateReady = false;
    mpHostStateFailed = false;

    mpHostStateSize = 0;
    mpHostStateCrc32 = 0;
    mpHostStateOffset = 0;
    mpHostStateChunkIndex = 0;
    mpHostStateCurrentChunkSize = 0;

    mpHostStateManifestSendCounter = 0;
    mpHostStateChunkSendCounter = 0;

    memset(
        &mpHostStateCurrentChunk,
        0,
        sizeof(mpHostStateCurrentChunk)
    );
}


static void mpResetClientStateTransfer(bool deleteFile)
{
    if (mpClientStateFile)
    {
        fclose(mpClientStateFile);
        mpClientStateFile = NULL;
    }

    if (deleteFile)
        remove(MP_CLIENT_STATE_PATH);

    mpClientStateManifestReceived = false;
    mpClientStateReady = false;
    mpClientStateFailed = false;

    mpClientExpectedStateSize = 0;
    mpClientExpectedStateCrc32 = 0;
    mpClientStateReceivedSize = 0;
    mpClientStateExpectedChunk = 0;
    mpClientStateCrcState = 0xFFFFFFFF;

    mpClientStateReadySendCounter = 0;
}


void impl3dsLocalPlayStop()
{

    mpResetHostStateTransfer(true);
    mpResetClientStateTransfer(true);
    mpRemoteKeys = 0;
    mpDiscoveredCount = 0;

    mpLatestP2Buttons = 0;
    mpLatestSyncInput = 0;
    mpHaveSyncInput = false;

    mpClientInputSequence = 0;
    mpHostInputSequence = 0;

    mpLockstepFrame = 0;
    mpLockstepInitialized = false;
    mpHostHavePreviousSync = false;
    memset(&mpHostPreviousSync, 0, sizeof(mpHostPreviousSync));

    mpLastSentP2Buttons = 0xFF;
    mpP2HeartbeatFrames = 0;

    mpHaveP2Sequence = false;
    mpLastP2Sequence = 0;
    mpP2FramesSincePacket = 0;

    mpHostRomSize = 0;
    mpHostGameName[0] = '\0';

    mpResetHostTransfer();
    mpResetClientTransfer(true);

    mpHostRomSize = 0;
    mpHostRomCrc32 = 0;
    mpHostRomPath[0] = '\0';

    if (mpHostActive)
    {
        udsDestroyNetwork();
        udsUnbind(&mpBindCtx);
        mpHostActive = false;
    }
    else if (mpClientActive)
    {
        udsDisconnectNetwork();
        udsUnbind(&mpBindCtx);
        mpClientActive = false;
    }

    if (mpUdsInitialized)
    {
        udsExit();
        mpUdsInitialized = false;
    }
}


static bool mpClientSendP2Input(u8 buttons)
{
    if (!mpClientActive)
        return false;

    MpP2InputPacket packet = {};

    memcpy(packet.header.magic, "VNMP", 4);
    packet.header.version = MP_LOBBY_VERSION;
    packet.header.type = MP_PACKET_P2_INPUT;
    packet.header.payloadSize =
        sizeof(packet) - sizeof(packet.header);

    packet.sequence = mpClientInputSequence;
    packet.buttons = buttons;

    Result ret = udsSendTo(
        UDS_HOST_NETWORKNODEID,
        MP_DATA_CHANNEL,
        UDS_SENDFLAG_Default,
        &packet,
        sizeof(packet)
    );

    // Only advance sequence if this packet was actually sent.
    if (R_SUCCEEDED(ret))
    {
        mpClientInputSequence++;
        return true;
    }

    return false;
}


static void mpHostPollP2Input()
{
    if (!mpHostActive)
        return;

    mpP2FramesSincePacket++;

    for (int i = 0; i < 8; i++)
    {
        u8 buffer[UDS_DATAFRAME_MAXSIZE] = {};
        size_t receivedSize = 0;
        u16 sourceNode = 0;

        Result ret = udsPullPacket(
            &mpBindCtx,
            buffer,
            sizeof(buffer),
            &receivedSize,
            &sourceNode
        );

        if (R_FAILED(ret) || receivedSize == 0)
            break;

        if (receivedSize < sizeof(MpPacketHeader))
            continue;

        MpPacketHeader *header =
            (MpPacketHeader *)buffer;

        if (memcmp(header->magic, "VNMP", 4) != 0 ||
            header->version != MP_LOBBY_VERSION)
        {
            continue;
        }

        if (header->type == MP_PACKET_P2_INPUT &&
            receivedSize == sizeof(MpP2InputPacket))
        {
            MpP2InputPacket *packet =
                (MpP2InputPacket *)buffer;

            bool newer =
                !mpHaveP2Sequence ||
                (s32)(packet->sequence - mpLastP2Sequence) > 0;

            if (newer)
            {
                mpHaveP2Sequence = true;
                mpLastP2Sequence = packet->sequence;

                mpLatestP2Buttons = packet->buttons;
                mpP2FramesSincePacket = 0;
            }
        }
    }

    // Never allow a lost/disconnected controller packet
    // to leave a NES button held forever.
    //
    // ~15 frames = ~250 ms at 60 fps.
    if (mpP2FramesSincePacket > 15)
        mpLatestP2Buttons = 0;
}


static void mpHostSendSyncInput(u16 buttons)
{
    if (!mpHostActive)
        return;

    MpSyncInputPacket packet = {};

    memcpy(packet.header.magic, "VNMP", 4);
    packet.header.version = MP_LOBBY_VERSION;
    packet.header.type = MP_PACKET_SYNC_INPUT;
    packet.header.payloadSize =
        sizeof(packet) - sizeof(packet.header);

    packet.sequence = mpHostInputSequence++;
    packet.buttons = buttons;

    udsSendTo(
        UDS_BROADCAST_NETWORKNODEID,
        MP_DATA_CHANNEL,
        UDS_SENDFLAG_Default,
        &packet,
        sizeof(packet)
    );
}


static void mpClientPollSyncInput()
{
    if (!mpClientActive)
        return;

    for (int i = 0; i < 8; i++)
    {
        u8 buffer[UDS_DATAFRAME_MAXSIZE] = {};
        size_t receivedSize = 0;
        u16 sourceNode = 0;

        Result ret = udsPullPacket(
            &mpBindCtx,
            buffer,
            sizeof(buffer),
            &receivedSize,
            &sourceNode
        );

        if (R_FAILED(ret) || receivedSize == 0)
            break;

        if (receivedSize < sizeof(MpPacketHeader))
            continue;

        MpPacketHeader *header =
            (MpPacketHeader *)buffer;

        if (memcmp(header->magic, "VNMP", 4) != 0 ||
            header->version != MP_LOBBY_VERSION)
        {
            continue;
        }

        if (header->type == MP_PACKET_SYNC_INPUT &&
            receivedSize == sizeof(MpSyncInputPacket))
        {
            MpSyncInputPacket *packet =
                (MpSyncInputPacket *)buffer;

            mpLatestSyncInput = packet->buttons;
            mpHaveSyncInput = true;
        }
    }
}


#define MP_LOCKSTEP_STATUS_CHECK_MS 50
#define MP_LOCKSTEP_BUFFER_FRAMES 4
#define MP_LOCKSTEP_CACHE_SIZE 32

static bool mpHostP1Valid[
    MP_LOCKSTEP_CACHE_SIZE
] = {};

static u32 mpHostP1Frame[
    MP_LOCKSTEP_CACHE_SIZE
] = {};

static u8 mpHostP1Buttons[
    MP_LOCKSTEP_CACHE_SIZE
] = {};


static bool mpHostP2Valid[
    MP_LOCKSTEP_CACHE_SIZE
] = {};

static u32 mpHostP2Frame[
    MP_LOCKSTEP_CACHE_SIZE
] = {};

static u8 mpHostP2Buttons[
    MP_LOCKSTEP_CACHE_SIZE
] = {};


static bool mpHostSyncValid[
    MP_LOCKSTEP_CACHE_SIZE
] = {};

static u32 mpHostSyncFrame[
    MP_LOCKSTEP_CACHE_SIZE
] = {};

static u16 mpHostSyncButtons[
    MP_LOCKSTEP_CACHE_SIZE
] = {};


static bool mpClientP2Valid[
    MP_LOCKSTEP_CACHE_SIZE
] = {};

static u32 mpClientP2Frame[
    MP_LOCKSTEP_CACHE_SIZE
] = {};

static u8 mpClientP2Buttons[
    MP_LOCKSTEP_CACHE_SIZE
] = {};


static bool mpClientSyncValid[
    MP_LOCKSTEP_CACHE_SIZE
] = {};

static u32 mpClientSyncFrame[
    MP_LOCKSTEP_CACHE_SIZE
] = {};

static u16 mpClientSyncButtons[
    MP_LOCKSTEP_CACHE_SIZE
] = {};


static bool mpHostPrefillStarted = false;
static bool mpClientPrefillStarted = false;
static void mpHostStoreP1(
    u32 frame,
    u8 buttons)
{
    u32 i = frame % MP_LOCKSTEP_CACHE_SIZE;

    mpHostP1Frame[i] = frame;
    mpHostP1Buttons[i] = buttons;
    mpHostP1Valid[i] = true;
}


static bool mpHostGetP1(
    u32 frame,
    u8 *buttonsOut)
{
    u32 i = frame % MP_LOCKSTEP_CACHE_SIZE;

    if (!mpHostP1Valid[i] ||
        mpHostP1Frame[i] != frame)
    {
        return false;
    }

    if (buttonsOut)
        *buttonsOut = mpHostP1Buttons[i];

    return true;
}


static void mpHostStoreP2(
    u32 frame,
    u8 buttons)
{
    u32 i = frame % MP_LOCKSTEP_CACHE_SIZE;

    mpHostP2Frame[i] = frame;
    mpHostP2Buttons[i] = buttons;
    mpHostP2Valid[i] = true;
}


static bool mpHostGetP2(
    u32 frame,
    u8 *buttonsOut)
{
    u32 i = frame % MP_LOCKSTEP_CACHE_SIZE;

    if (!mpHostP2Valid[i] ||
        mpHostP2Frame[i] != frame)
    {
        return false;
    }

    if (buttonsOut)
        *buttonsOut = mpHostP2Buttons[i];

    return true;
}


static void mpHostStoreSync(
    u32 frame,
    u16 buttons)
{
    u32 i = frame % MP_LOCKSTEP_CACHE_SIZE;

    mpHostSyncFrame[i] = frame;
    mpHostSyncButtons[i] = buttons;
    mpHostSyncValid[i] = true;
}


static bool mpHostGetSync(
    u32 frame,
    u16 *buttonsOut)
{
    u32 i = frame % MP_LOCKSTEP_CACHE_SIZE;

    if (!mpHostSyncValid[i] ||
        mpHostSyncFrame[i] != frame)
    {
        return false;
    }

    if (buttonsOut)
        *buttonsOut = mpHostSyncButtons[i];

    return true;
}


static void mpClientStoreP2(
    u32 frame,
    u8 buttons)
{
    u32 i = frame % MP_LOCKSTEP_CACHE_SIZE;

    mpClientP2Frame[i] = frame;
    mpClientP2Buttons[i] = buttons;
    mpClientP2Valid[i] = true;
}


static bool mpClientGetP2(
    u32 frame,
    u8 *buttonsOut)
{
    u32 i = frame % MP_LOCKSTEP_CACHE_SIZE;

    if (!mpClientP2Valid[i] ||
        mpClientP2Frame[i] != frame)
    {
        return false;
    }

    if (buttonsOut)
        *buttonsOut = mpClientP2Buttons[i];

    return true;
}


static void mpClientStoreSync(
    u32 frame,
    u16 buttons)
{
    u32 i = frame % MP_LOCKSTEP_CACHE_SIZE;

    mpClientSyncFrame[i] = frame;
    mpClientSyncButtons[i] = buttons;
    mpClientSyncValid[i] = true;
}


static bool mpClientTakeSync(
    u32 frame,
    u16 *buttonsOut)
{
    u32 i = frame % MP_LOCKSTEP_CACHE_SIZE;

    if (!mpClientSyncValid[i] ||
        mpClientSyncFrame[i] != frame)
    {
        return false;
    }

    if (buttonsOut)
        *buttonsOut = mpClientSyncButtons[i];

    mpClientSyncValid[i] = false;

    return true;
}



static void mpInitializeLockstep()
{
    if (mpLockstepInitialized)
        return;

    mpLockstepFrame = 0;

    mpHostHavePreviousSync = false;

    memset(
        &mpHostPreviousSync,
        0,
        sizeof(mpHostPreviousSync)
    );

    memset(mpHostP1Valid, 0, sizeof(mpHostP1Valid));
    memset(mpHostP2Valid, 0, sizeof(mpHostP2Valid));
    memset(mpHostSyncValid, 0, sizeof(mpHostSyncValid));

    memset(mpClientP2Valid, 0, sizeof(mpClientP2Valid));
    memset(mpClientSyncValid, 0, sizeof(mpClientSyncValid));

    mpHostPrefillStarted = false;
    mpClientPrefillStarted = false;

    mpLockstepInitialized = true;
}
static bool mpLockstepSendRaw(
    u16 destination,
    const void *data,
    size_t size)
{
    for (int attempt = 0; attempt < 4; attempt++)
    {
        Result ret = udsSendTo(
            destination,
            MP_DATA_CHANNEL,
            UDS_SENDFLAG_Default,
            data,
            size
        );

        if (R_SUCCEEDED(ret))
            return true;

        if (UDS_CHECK_SENDTO_FATALERROR(ret))
            return false;

        svcSleepThread(250000);
    }

    return false;
}
static void mpLockstepSendP2(u32 frame, u8 buttons)
{
    MpP2InputPacket packet = {};

    memcpy(packet.header.magic, "VNMP", 4);
    packet.header.version = MP_LOBBY_VERSION;
    packet.header.type = MP_PACKET_P2_INPUT;
    packet.header.payloadSize =
        sizeof(packet) - sizeof(packet.header);

    packet.sequence = frame;
    packet.buttons = buttons;

    mpLockstepSendRaw(
        UDS_HOST_NETWORKNODEID,
        &packet,
        sizeof(packet)
    );
}
static void mpLockstepSendSync(
    u32 frame,
    u16 buttons)
{
    MpSyncInputPacket packet = {};

    memcpy(packet.header.magic, "VNMP", 4);
    packet.header.version = MP_LOBBY_VERSION;
    packet.header.type = MP_PACKET_SYNC_INPUT;
    packet.header.payloadSize =
        sizeof(packet) - sizeof(packet.header);

    packet.sequence = frame;
    packet.buttons = buttons;

    mpHostStoreSync(
        frame,
        buttons
    );

    mpLockstepSendRaw(
        UDS_BROADCAST_NETWORKNODEID,
        &packet,
        sizeof(packet)
    );

    mpHostPreviousSync = packet;
    mpHostHavePreviousSync = true;
}

static void mpLockstepSendSyncRequest(u32 frame)
{
    MpSyncRequestPacket packet = {};

    memcpy(packet.header.magic, "VNMP", 4);
    packet.header.version = MP_LOBBY_VERSION;
    packet.header.type = MP_PACKET_SYNC_REQUEST;
    packet.header.payloadSize =
        sizeof(packet) - sizeof(packet.header);

    packet.sequence = frame;

    mpLockstepSendRaw(
        UDS_HOST_NETWORKNODEID,
        &packet,
        sizeof(packet)
    );
}
static bool mpLockstepHostTryBuildSync(u32 frame)
{
    u16 existing = 0;

    if (mpHostGetSync(frame, &existing))
        return true;

    u8 p1 = 0;
    u8 p2 = 0;

    if (!mpHostGetP1(frame, &p1) ||
        !mpHostGetP2(frame, &p2))
    {
        return false;
    }

    u16 synchronizedInput =
        (u16)p1 |
        ((u16)p2 << 8);

    mpLockstepSendSync(
        frame,
        synchronizedInput
    );

    return true;
}


static bool mpLockstepHostResendSync(u32 frame)
{
    u16 buttons = 0;

    if (!mpHostGetSync(
            frame,
            &buttons))
    {
        return false;
    }

    MpSyncInputPacket packet = {};

    memcpy(packet.header.magic, "VNMP", 4);
    packet.header.version = MP_LOBBY_VERSION;
    packet.header.type = MP_PACKET_SYNC_INPUT;
    packet.header.payloadSize =
        sizeof(packet) - sizeof(packet.header);

    packet.sequence = frame;
    packet.buttons = buttons;

    mpLockstepSendRaw(
        UDS_BROADCAST_NETWORKNODEID,
        &packet,
        sizeof(packet)
    );

    return true;
}
static void mpLockstepHostPump(u32 currentFrame)
{
    for (int n = 0; n < 32; n++)
    {
        u8 buffer[UDS_DATAFRAME_MAXSIZE] = {};
        size_t receivedSize = 0;
        u16 sourceNode = 0;

        Result ret = udsPullPacket(
            &mpBindCtx,
            buffer,
            sizeof(buffer),
            &receivedSize,
            &sourceNode
        );

        if (R_FAILED(ret) ||
            receivedSize == 0)
        {
            break;
        }

        if (receivedSize <
            sizeof(MpPacketHeader))
        {
            continue;
        }

        MpPacketHeader *header =
            (MpPacketHeader *)buffer;

        if (memcmp(
                header->magic,
                "VNMP",
                4) != 0 ||
            header->version !=
                MP_LOBBY_VERSION)
        {
            continue;
        }
        if (header->type ==
                MP_PACKET_P2_INPUT &&
            receivedSize ==
                sizeof(MpP2InputPacket))
        {
            MpP2InputPacket *packet =
                (MpP2InputPacket *)buffer;

            if (packet->sequence < currentFrame)
            {
                mpLockstepHostResendSync(
                    packet->sequence
                );

                continue;
            }

            if (packet->sequence >=
                currentFrame +
                MP_LOCKSTEP_CACHE_SIZE)
            {
                continue;
            }

            mpHostStoreP2(
                packet->sequence,
                packet->buttons
            );

            continue;
        }
        if (header->type ==
                MP_PACKET_SYNC_REQUEST &&
            receivedSize ==
                sizeof(MpSyncRequestPacket))
        {
            MpSyncRequestPacket *packet =
                (MpSyncRequestPacket *)buffer;

            mpLockstepHostResendSync(
                packet->sequence
            );

            continue;
        }
    }
    for (
        u32 offset = 0;
        offset < MP_LOCKSTEP_BUFFER_FRAMES + 4;
        offset++)
    {
        mpLockstepHostTryBuildSync(
            currentFrame + offset
        );
    }
}
static bool mpLockstepHostGetSync(
    u32 frame,
    u8 sampledPlayer1,
    u16 *buttonsOut)
{
    if (!mpHostPrefillStarted)
    {
        for (
            u32 i = 0;
            i < MP_LOCKSTEP_BUFFER_FRAMES;
            i++)
        {
            mpHostStoreP1(
                i,
                sampledPlayer1
            );
        }

        mpHostPrefillStarted = true;
    }
    u32 futureFrame =
        frame +
        MP_LOCKSTEP_BUFFER_FRAMES;

    mpHostStoreP1(
        futureFrame,
        sampledPlayer1
    );
    mpLockstepHostPump(frame);

    mpLockstepHostTryBuildSync(
        futureFrame
    );

    if (mpHostGetSync(
            frame,
            buttonsOut))
    {
        return true;
    }
    u64 lastStatusCheck = 0;

    while (true)
    {
        u64 now = osGetTime();

        if (lastStatusCheck == 0 ||
            now - lastStatusCheck >=
                MP_LOCKSTEP_STATUS_CHECK_MS)
        {
            lastStatusCheck = now;

            if (!mpHostActive ||
                !impl3dsLocalPlayHasGuest())
            {
                return false;
            }
        }

        mpLockstepHostPump(frame);

        mpLockstepHostTryBuildSync(
            frame
        );

        if (mpHostGetSync(
                frame,
                buttonsOut))
        {
            return true;
        }

        svcSleepThread(250000);
    }
}
static void mpLockstepClientPump(u32 currentFrame)
{
    for (int n = 0; n < 32; n++)
    {
        u8 buffer[UDS_DATAFRAME_MAXSIZE] = {};
        size_t receivedSize = 0;
        u16 sourceNode = 0;

        Result ret = udsPullPacket(
            &mpBindCtx,
            buffer,
            sizeof(buffer),
            &receivedSize,
            &sourceNode
        );

        if (R_FAILED(ret) ||
            receivedSize == 0)
        {
            break;
        }

        if (receivedSize <
            sizeof(MpPacketHeader))
        {
            continue;
        }

        MpPacketHeader *header =
            (MpPacketHeader *)buffer;

        if (memcmp(
                header->magic,
                "VNMP",
                4) != 0 ||
            header->version !=
                MP_LOBBY_VERSION)
        {
            continue;
        }

        if (header->type !=
                MP_PACKET_SYNC_INPUT ||
            receivedSize !=
                sizeof(MpSyncInputPacket))
        {
            continue;
        }

        MpSyncInputPacket *packet =
            (MpSyncInputPacket *)buffer;

        if (packet->sequence < currentFrame)
            continue;

        if (packet->sequence >=
            currentFrame +
            MP_LOCKSTEP_CACHE_SIZE)
        {
            continue;
        }

        mpClientStoreSync(
            packet->sequence,
            packet->buttons
        );
    }
}
static bool mpLockstepClientGetSync(
    u32 frame,
    u8 sampledPlayer2,
    u16 *buttonsOut)
{
    if (!mpClientPrefillStarted)
    {
        for (
            u32 i = 0;
            i < MP_LOCKSTEP_BUFFER_FRAMES;
            i++)
        {
            mpClientStoreP2(
                i,
                sampledPlayer2
            );

            mpLockstepSendP2(
                i,
                sampledPlayer2
            );
        }

        mpClientPrefillStarted = true;
    }
    u32 futureFrame =
        frame +
        MP_LOCKSTEP_BUFFER_FRAMES;

    mpClientStoreP2(
        futureFrame,
        sampledPlayer2
    );

    mpLockstepSendP2(
        futureFrame,
        sampledPlayer2
    );
    mpLockstepClientPump(frame);

    if (mpClientTakeSync(
            frame,
            buttonsOut))
    {
        return true;
    }
    u64 lastStatusCheck = 0;
    u64 lastRecoverySend = 0;

    while (true)
    {
        u64 now = osGetTime();

        if (lastStatusCheck == 0 ||
            now - lastStatusCheck >=
                MP_LOCKSTEP_STATUS_CHECK_MS)
        {
            lastStatusCheck = now;

            if (!mpClientActive ||
                !impl3dsLocalPlayClientHasHost())
            {
                return false;
            }
        }
        if (lastRecoverySend == 0 ||
            now - lastRecoverySend >= 4)
        {
            lastRecoverySend = now;

            u8 exactP2 = 0;

            if (mpClientGetP2(
                    frame,
                    &exactP2))
            {
                mpLockstepSendP2(
                    frame,
                    exactP2
                );
            }

            mpLockstepSendSyncRequest(
                frame
            );
        }


        mpLockstepClientPump(frame);

        if (mpClientTakeSync(
                frame,
                buttonsOut))
        {
            return true;
        }

        svcSleepThread(250000);
    }
}


static void mpPollRemote()
{
    if (!mpHostActive)
        return;

    u32 received = 0;
    size_t receivedSize = 0;
    u16 sourceNode = 0;

    Result ret = udsPullPacket(
        &mpBindCtx,
        &received,
        sizeof(received),
        &receivedSize,
        &sourceNode
    );

    if (R_SUCCEEDED(ret) && receivedSize == sizeof(received))
        mpRemoteKeys = received;
}


//----------------------------------------------------------------------
// Settings
//----------------------------------------------------------------------
SSettings3DS settings3DS;

//----------------------------------------------------------------------
// Menu options
//----------------------------------------------------------------------

SMenuItem optionsForFont[] = {
    MENU_MAKE_DIALOG_ACTION (0, "Tempesta",               ""),
    MENU_MAKE_DIALOG_ACTION (1, "Ronda",                  ""),
    MENU_MAKE_DIALOG_ACTION (2, "Arial",                  ""),
    MENU_MAKE_LASTITEM  ()
};

SMenuItem optionsForStretch[] = {
    MENU_MAKE_DIALOG_ACTION (0, "No Stretch",               "'Pixel Perfect'"),
    MENU_MAKE_DIALOG_ACTION (1, "4:3 Fit",                  "Stretch to 320x240"),
    MENU_MAKE_DIALOG_ACTION (2, "Fullscreen",               "Stretch to 400x240"),
    MENU_MAKE_DIALOG_ACTION (3, "Cropped 4:3 Fit",          "Crop & Stretch to 320x240"),
    MENU_MAKE_DIALOG_ACTION (4, "Cropped Fullscreen",       "Crop & Stretch to 400x240"),
    MENU_MAKE_LASTITEM  ()
};

SMenuItem optionsForFrameskip[] = {
    MENU_MAKE_DIALOG_ACTION (0, "Disabled",                 ""),
    MENU_MAKE_DIALOG_ACTION (1, "Enabled (max 1 frame)",    ""),
    MENU_MAKE_DIALOG_ACTION (2, "Enabled (max 2 frames)",    ""),
    MENU_MAKE_DIALOG_ACTION (3, "Enabled (max 3 frames)",    ""),
    MENU_MAKE_DIALOG_ACTION (4, "Enabled (max 4 frames)",    ""),
    MENU_MAKE_LASTITEM  ()
};

SMenuItem optionsForFrameRate[] = {
    MENU_MAKE_DIALOG_ACTION (0, "Default based on ROM",     ""),
    MENU_MAKE_DIALOG_ACTION (1, "50 FPS",                   ""),
    MENU_MAKE_DIALOG_ACTION (2, "60 FPS",                   ""),
    MENU_MAKE_LASTITEM  ()
};

SMenuItem optionsForAutoSaveSRAMDelay[] = {
    MENU_MAKE_DIALOG_ACTION (1, "1 second",     ""),
    MENU_MAKE_DIALOG_ACTION (2, "10 seconds",   ""),
    MENU_MAKE_DIALOG_ACTION (3, "60 seconds",   ""),
    MENU_MAKE_DIALOG_ACTION (4, "Disabled",     "Touch bottom screen to save"),
    MENU_MAKE_LASTITEM  ()
};

SMenuItem optionsForTurboFire[] = {
    MENU_MAKE_DIALOG_ACTION (0, "None",         ""),
    MENU_MAKE_DIALOG_ACTION (10, "Slowest",      ""),
    MENU_MAKE_DIALOG_ACTION (8, "Slower",       ""),
    MENU_MAKE_DIALOG_ACTION (6, "Slow",         ""),
    MENU_MAKE_DIALOG_ACTION (4, "Fast",         ""),
    MENU_MAKE_DIALOG_ACTION (2, "Faster",         ""),
    MENU_MAKE_DIALOG_ACTION (1, "Very Fast",    ""),
    MENU_MAKE_LASTITEM  ()
};

SMenuItem optionsForButtons[] = {
    MENU_MAKE_DIALOG_ACTION (0,             "None",             ""),
    MENU_MAKE_DIALOG_ACTION (BTNNES_A,      "NES 'A'",          ""),
    MENU_MAKE_DIALOG_ACTION (BTNNES_B,      "NES 'B'",          ""),
    MENU_MAKE_DIALOG_ACTION (BTNNES_SELECT, "NES 'SELECT'",     ""),
    MENU_MAKE_DIALOG_ACTION (BTNNES_START,  "NES 'START'",      ""),
    MENU_MAKE_LASTITEM  ()
};

SMenuItem optionsFor3DSButtons[] = {
    MENU_MAKE_DIALOG_ACTION (0,                 "None",             ""),
    MENU_MAKE_DIALOG_ACTION (KEY_A,             "3DS A Button",     ""),
    MENU_MAKE_DIALOG_ACTION (KEY_B,             "3DS B Button",     ""),
    MENU_MAKE_DIALOG_ACTION (KEY_X,             "3DS X Button",     ""),
    MENU_MAKE_DIALOG_ACTION (KEY_Y,             "3DS Y Button",     ""),
    MENU_MAKE_DIALOG_ACTION (KEY_L,             "3DS L Button",     ""),
    MENU_MAKE_DIALOG_ACTION (KEY_R,             "3DS R Button",     ""),
    MENU_MAKE_DIALOG_ACTION (KEY_ZL,            "New 3DS ZL Button",     ""),
    MENU_MAKE_DIALOG_ACTION (KEY_ZR,            "New 3DS ZR Button",     ""),
    MENU_MAKE_LASTITEM  ()
};


SMenuItem optionsForSpriteFlicker[] =
{
    MENU_MAKE_DIALOG_ACTION (0, "Hardware Accurate",   "Flickers like real hardware"),
    MENU_MAKE_DIALOG_ACTION (1, "Better Visuals",      "Looks better, less accurate"),
    MENU_MAKE_LASTITEM  ()  
};

SMenuItem optionMenu[] = {
    MENU_MAKE_HEADER1   ("GLOBAL SETTINGS"),
    MENU_MAKE_PICKER    (11000, "  Screen Stretch", "How would you like the final screen to appear?", optionsForStretch, DIALOGCOLOR_CYAN),
    MENU_MAKE_PICKER    (18000, "  Font", "The font used for the user interface.", optionsForFont, DIALOGCOLOR_CYAN),
    MENU_MAKE_CHECKBOX  (15001, "  Hide text in bottom screen", 0),
    MENU_MAKE_DISABLED  (""),
    MENU_MAKE_CHECKBOX  (21000, "  Automatically save state on exit and load state on start", 0),
    MENU_MAKE_DISABLED  (""),
    MENU_MAKE_HEADER1   ("GAME-SPECIFIC SETTINGS"),
    MENU_MAKE_PICKER    (10000, "  Frameskip", "Try changing this if the game runs slow. Skipping frames help it run faster but less smooth.", optionsForFrameskip, DIALOGCOLOR_CYAN),
    MENU_MAKE_PICKER    (12000, "  Framerate", "Some games run at 50 or 60 FPS by default. Override if required.", optionsForFrameRate, DIALOGCOLOR_CYAN),
    MENU_MAKE_PICKER    (19000, "  Flickering Sprites", "Sprites on real hardware flicker. You can disable for better visuals.", optionsForSpriteFlicker, DIALOGCOLOR_CYAN),
    MENU_MAKE_DISABLED  (""),
    MENU_MAKE_HEADER1   ("AUDIO"),
    MENU_MAKE_CHECKBOX  (20002, "  Apply volume to all games", 0),
    MENU_MAKE_GAUGE     (14000, "  Volume Amplification", 0, 8, 4),
    MENU_MAKE_LASTITEM  ()
};


SMenuItem controlsMenu[] = {
    MENU_MAKE_HEADER1   ("BUTTON CONFIGURATION"),
    MENU_MAKE_CHECKBOX  (20000, "  Apply button mappings to all games", 0),
    MENU_MAKE_CHECKBOX  (20001, "  Apply rapid fire settings to all games", 0),
    MENU_MAKE_DISABLED  (""),
    MENU_MAKE_HEADER2   ("3DS A Button"),
    MENU_MAKE_PICKER    (13010, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_PICKER    (13020, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_GAUGE     (13000, "  Rapid-Fire Speed", 0, 10, 0),
    MENU_MAKE_DISABLED  (""),
    MENU_MAKE_HEADER2   ("3DS B Button"),
    MENU_MAKE_PICKER    (13011, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_PICKER    (13021, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_GAUGE     (13001, "  Rapid-Fire Speed", 0, 10, 0),
    MENU_MAKE_DISABLED  (""),
    MENU_MAKE_HEADER2   ("3DS X Button"),
    MENU_MAKE_PICKER    (13012, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_PICKER    (13022, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_GAUGE     (13002, "  Rapid-Fire Speed", 0, 10, 0),
    MENU_MAKE_DISABLED  (""),
    MENU_MAKE_HEADER2   ("3DS Y Button"),
    MENU_MAKE_PICKER    (13013, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_PICKER    (13023, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_GAUGE     (13003, "  Rapid-Fire Speed", 0, 10, 0),
    MENU_MAKE_DISABLED  (""),
    MENU_MAKE_HEADER2   ("3DS L Button"),
    MENU_MAKE_PICKER    (13014, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_PICKER    (13024, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_GAUGE     (13004, "  Rapid-Fire Speed", 0, 10, 0),
    MENU_MAKE_DISABLED  (""),
    MENU_MAKE_HEADER2   ("3DS R Button"),
    MENU_MAKE_PICKER    (13015, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_PICKER    (13025, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_GAUGE     (13005, "  Rapid-Fire Speed", 0, 10, 0),
    MENU_MAKE_DISABLED  (""),
    MENU_MAKE_HEADER2   ("New 3DS ZL Button"),
    MENU_MAKE_PICKER    (13016, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_PICKER    (13026, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_GAUGE     (13006, "  Rapid-Fire Speed", 0, 10, 0),
    MENU_MAKE_DISABLED  (""),
    MENU_MAKE_HEADER2   ("New 3DS ZR Button"),
    MENU_MAKE_PICKER    (13017, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_PICKER    (13027, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_GAUGE     (13007, "  Rapid-Fire Speed", 0, 10, 0),
    MENU_MAKE_DISABLED  (""),
    MENU_MAKE_HEADER2   ("3DS SELECT Button"),
    MENU_MAKE_PICKER    (13018, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_PICKER    (13028, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_DISABLED  (""),
    MENU_MAKE_HEADER2   ("3DS START Button"),
    MENU_MAKE_PICKER    (13019, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_PICKER    (13029, "  Maps to", "", optionsForButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_DISABLED  (""),
    MENU_MAKE_HEADER1   ("EMULATOR FUNCTIONS"),
    MENU_MAKE_CHECKBOX  (50003, "Apply keys to all games", 0),
    MENU_MAKE_PICKER    (23001, "Open Emulator Menu", "", optionsFor3DSButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_PICKER    (23002, "Fast Forward", "", optionsFor3DSButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_DISABLED  ("  (Works better on N3DS. May freeze/corrupt games.)"),
    MENU_MAKE_PICKER    (23003, "Insert Coin 1 (VS Games)", "", optionsFor3DSButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_PICKER    (23004, "Insert Coin 2 (VS Games)", "", optionsFor3DSButtons, DIALOGCOLOR_CYAN),
    MENU_MAKE_LASTITEM  ()
};


//-------------------------------------------------------
SMenuItem optionsForDisk[] =
{
    MENU_MAKE_DIALOG_ACTION (0, "Eject Disk",               ""),
    MENU_MAKE_DIALOG_ACTION (1, "Change to Disk 1 Side A",  ""),
    MENU_MAKE_DIALOG_ACTION (2, "Change to Disk 1 Side B",  ""),
    MENU_MAKE_DIALOG_ACTION (3, "Change to Disk 2 Side A",  ""),
    MENU_MAKE_DIALOG_ACTION (4, "Change to Disk 2 Side B",  ""),
    MENU_MAKE_DIALOG_ACTION (5, "Change to Disk 3 Side A",  ""),
    MENU_MAKE_DIALOG_ACTION (6, "Change to Disk 3 Side B",  ""),
    MENU_MAKE_DIALOG_ACTION (7, "Change to Disk 4 Side A",  ""),
    MENU_MAKE_DIALOG_ACTION (8, "Change to Disk 4 Side B",  ""),
    MENU_MAKE_LASTITEM  ()  
};


//-------------------------------------------------------
// Standard in-game emulator menu.
// You should not modify those menu items that are
// marked 'do not modify'.
//-------------------------------------------------------
SMenuItem emulatorMenu[] = {
    MENU_MAKE_HEADER2   ("Emulator"),               // Do not modify
    MENU_MAKE_ACTION    (1000, "  Resume Game"),    // Do not modify
    MENU_MAKE_PICKER2   (30000,"  Choose Disk", "", optionsForDisk, DIALOGCOLOR_CYAN),
    MENU_MAKE_HEADER2   (""),

    MENU_MAKE_HEADER2   ("Savestates"),
    MENU_MAKE_ACTION    (2001, "  Save Slot #1"),   // Do not modify
    MENU_MAKE_ACTION    (2002, "  Save Slot #2"),   // Do not modify
    MENU_MAKE_ACTION    (2003, "  Save Slot #3"),   // Do not modify
    MENU_MAKE_ACTION    (2004, "  Save Slot #4"),   // Do not modify
    MENU_MAKE_ACTION    (2005, "  Save Slot #5"),   // Do not modify
    MENU_MAKE_HEADER2   (""),   
    
    MENU_MAKE_ACTION    (3001, "  Load Slot #1"),   // Do not modify
    MENU_MAKE_ACTION    (3002, "  Load Slot #2"),   // Do not modify
    MENU_MAKE_ACTION    (3003, "  Load Slot #3"),   // Do not modify
    MENU_MAKE_ACTION    (3004, "  Load Slot #4"),   // Do not modify
    MENU_MAKE_ACTION    (3005, "  Load Slot #5"),   // Do not modify
    MENU_MAKE_HEADER2   (""),

    MENU_MAKE_HEADER2   ("Others"),                 // Do not modify
    MENU_MAKE_ACTION    (4001, "  Take Screenshot"),// Do not modify
    MENU_MAKE_ACTION    (5001, "  Reset Console"),  // Do not modify
    MENU_MAKE_ACTION    (6001, "  Exit"),           // Do not modify
    MENU_MAKE_LASTITEM  ()
    };





//------------------------------------------------------------------------
// Memory Usage = 0.003 MB   for 4-point rectangle (triangle strip) vertex buffer
#define RECTANGLE_BUFFER_SIZE           0x1000

//------------------------------------------------------------------------
// Memory Usage = 0.003 MB   for 6-point quad vertex buffer (Citra only)
#define CITRA_VERTEX_BUFFER_SIZE        0x1000

// Memory Usage = Not used (Real 3DS only)
#define CITRA_TILE_BUFFER_SIZE          0x1000


//------------------------------------------------------------------------
// Memory Usage = 0.003 MB   for 6-point quad vertex buffer (Real 3DS only)
#define REAL3DS_VERTEX_BUFFER_SIZE      0x1000

// Memory Usage = 0.003 MB   for 2-point rectangle vertex buffer (Real 3DS only)
#define REAL3DS_TILE_BUFFER_SIZE        0x1000


//---------------------------------------------------------
// Our textures
//---------------------------------------------------------

NES* nes = NULL;

unsigned char linecolor[256];



//---------------------------------------------------------
// Settings related to the emulator.
//---------------------------------------------------------
extern SSettings3DS settings3DS;


//---------------------------------------------------------
// Provide a comma-separated list of file extensions
//---------------------------------------------------------
char *impl3dsRomExtensions = "nes,fds";


//---------------------------------------------------------
// The title image .PNG filename.
//---------------------------------------------------------
char *impl3dsTitleImage = "./virtuanes_3ds_top.png";


//---------------------------------------------------------
// The title that displays at the bottom right of the
// menu.
//---------------------------------------------------------
char *impl3dsTitleText = "VirtuaNES for 3DS v1.02";


//---------------------------------------------------------
// The bitmaps for the emulated console's UP, DOWN, LEFT, 
// RIGHT keys.
//---------------------------------------------------------
u32 input3dsDKeys[4] = { BTNNES_UP, BTNNES_DOWN, BTNNES_LEFT, BTNNES_RIGHT };


//---------------------------------------------------------
// The list of valid joypad bitmaps for the emulated 
// console.
//
// This should NOT include D-keys.
//---------------------------------------------------------
u32 input3dsValidButtonMappings[10] = { BTNNES_A, BTNNES_B, BTNNES_SELECT, BTNNES_START, 0, 0, 0, 0, 0, 0 };


//---------------------------------------------------------
// The maps for the 10 3DS keys to the emulated consoles
// joypad bitmaps for the following 3DS keys (in order):
//   A, B, X, Y, L, R, ZL, ZR, SELECT, START
//
// This should NOT include D-keys.
//---------------------------------------------------------
u32 input3dsDefaultButtonMappings[10] = { BTNNES_A, BTNNES_B, BTNNES_A, BTNNES_B, 0, 0, 0, 0, BTNNES_SELECT, BTNNES_START };


//---------------------------------------------------------
// Initializes the emulator core.
//---------------------------------------------------------
bool impl3dsInitializeCore()
{
	nespalInitialize();

	// Initialize our GPU.
	// Load up and initialize any shaders
	//
    if (emulator.isReal3DS)
    {
    	gpu3dsLoadShader(0, (u32 *)shaderslow_shbin, shaderslow_shbin_size, 0);     // copy to screen
    	gpu3dsLoadShader(1, (u32 *)shaderfast2_shbin, shaderfast2_shbin_size, 6);   // draw tiles
    }
    else
    {
    	gpu3dsLoadShader(0, (u32 *)shaderslow_shbin, shaderslow_shbin_size, 0);     // copy to screen
        gpu3dsLoadShader(1, (u32 *)shaderslow2_shbin, shaderslow2_shbin_size, 0);   // draw tiles
    }

	gpu3dsInitializeShaderRegistersForRenderTarget(0, 10);
	gpu3dsInitializeShaderRegistersForTexture(4, 14);
	gpu3dsInitializeShaderRegistersForTextureOffset(6);
	
	
    // Create all the necessary textures
    //
    //nesTileCacheTexture = gpu3dsCreateTextureInLinearMemory(1024, 1024, GPU_RGBA5551);
 
    if (!video3dsInitializeSoftwareRendering(512, 256, GX_TRANSFER_FMT_RGB565))
        return false;

	// allocate all necessary vertex lists
	//
    if (emulator.isReal3DS)
    {
        gpu3dsAllocVertexList(&GPU3DSExt.rectangleVertexes, RECTANGLE_BUFFER_SIZE, sizeof(SVertexColor), 2, SVERTEXCOLOR_ATTRIBFORMAT);
        gpu3dsAllocVertexList(&GPU3DSExt.quadVertexes, REAL3DS_VERTEX_BUFFER_SIZE, sizeof(SVertexTexCoord), 2, SVERTEXTEXCOORD_ATTRIBFORMAT);
        gpu3dsAllocVertexList(&GPU3DSExt.tileVertexes, REAL3DS_TILE_BUFFER_SIZE, sizeof(SVertexTexCoord), 2, SVERTEXTEXCOORD_ATTRIBFORMAT);
    }
    else
    {
        gpu3dsAllocVertexList(&GPU3DSExt.rectangleVertexes, RECTANGLE_BUFFER_SIZE, sizeof(SVertexColor), 2, SVERTEXCOLOR_ATTRIBFORMAT);
        gpu3dsAllocVertexList(&GPU3DSExt.quadVertexes, CITRA_VERTEX_BUFFER_SIZE, sizeof(SVertexTexCoord), 2, SVERTEXTEXCOORD_ATTRIBFORMAT);
        gpu3dsAllocVertexList(&GPU3DSExt.tileVertexes, CITRA_TILE_BUFFER_SIZE, sizeof(SVertexTexCoord), 2, SVERTEXTEXCOORD_ATTRIBFORMAT);
    }

    if (GPU3DSExt.quadVertexes.ListBase == NULL ||
        GPU3DSExt.tileVertexes.ListBase == NULL ||
        GPU3DSExt.rectangleVertexes.ListBase == NULL)
    {
        printf ("Unable to allocate vertex list buffers \n");
        return false;
    }

	gpu3dsUseShader(0);
    return true;
}


//---------------------------------------------------------
// Finalizes and frees up any resources.
//---------------------------------------------------------
void impl3dsFinalize()
{
    video3dsFinalize();

	if (nes) delete nes;
}


int soundSamplesPerGeneration = 0;
int soundSamplesPerSecond = 0;
short soundSamples[1000];

//---------------------------------------------------------
// Mix sound samples into a temporary buffer.
//
// This gives time for the sound generation to execute
// from the 2nd core before copying it to the actual
// output buffer.
//---------------------------------------------------------
void impl3dsGenerateSoundSamples(int numberOfSamples)
{
	if (nes && soundSamplesPerGeneration)
	{
		nes->apu->Process((unsigned char *)soundSamples, soundSamplesPerGeneration * 2, emulator.fastForwarding);
	}
}


//---------------------------------------------------------
// Mix sound samples into a temporary buffer.
//
// This gives time for the sound generation to execute
// from the 2nd core before copying it to the actual
// output buffer.
// 
// For a console with only MONO output, simply copy
// the samples into the leftSamples buffer.
//---------------------------------------------------------
void impl3dsOutputSoundSamples(int numberOfSamples, short *leftSamples, short *rightSamples)
{
	for (int i = 0; i < soundSamplesPerGeneration; i++)
	{
		leftSamples[i] = soundSamples[i];
	}
}


//---------------------------------------------------------
// This is called when a ROM needs to be loaded and the
// emulator engine initialized.
//---------------------------------------------------------
bool impl3dsLoadROM(char *romFilePath)
{
	if (nes)
    {
		delete nes;
        nes = NULL;
    }

	nes = new NES(romFilePath);

if (nes->error)
{
    FILE *f = fopen("sdmc:/virtuanes_rom_error.txt", "w");

    if (f)
    {
        fprintf(f, "Path: %s\n", romFilePath);
        fprintf(f, "NES error: %s\n",
                nes->error ? nes->error : "(none)");

        if (nes->rom)
        {
            fprintf(f, "ROM error: %s\n",
                    nes->rom->error ? nes->rom->error : "(none)");
        }

        fclose(f);
    }

    return false;
}

	//nes->ppu->SetScreenPtr( NULL, linecolor );
	nes->ppu->SetScreenRGBAPtr( video3dsGetCurrentSoftwareBuffer(), linecolor );

	// compute a sample rate closes to 32000 kHz.
	//
    int nesSampleRate = 32000;
    bool new3DS = false;
    APT_CheckNew3DS(&new3DS);

    // Lagrange Point and Old 3DS, we need to use a lower sample rate
    // because the 2nd core is not fast enough to generate VRC7 sounds.
    //
    if (nes->rom->GetMapperNo() == 85 && !new3DS)   
        nesSampleRate = 20000;

    int numberOfGenerationsPerSecond = nes->nescfg->FrameRate * 2;
    soundSamplesPerGeneration = snd3dsComputeSamplesPerLoop(nesSampleRate, numberOfGenerationsPerSecond);
	soundSamplesPerSecond = snd3dsComputeSampleRate(nesSampleRate, numberOfGenerationsPerSecond);
	snd3dsSetSampleRate(
		false,
		nesSampleRate, 
		numberOfGenerationsPerSecond, 
		true, 
        1, 4);
	
	Config.sound.nRate = soundSamplesPerSecond;
	Config.sound.nBits = 16;
	Config.sound.nFilterType = 1;
	Config.sound.nVolume[0] = 200;
    Config.graphics.bAllSprite = 0;

	nes->Reset();

    // If this is a FDS game, enable the FDS menu.
    //
    int fdsDiskNo = nes->rom->GetDiskNo();

    for (int i = 0; ; i++)
    {
        if (emulatorMenu[i].Type == MENUITEM_LASTITEM)
            break;
        if (emulatorMenu[i].ID == 30000)
        {
            if (fdsDiskNo > 0) 
                emulatorMenu[i].Type = MENUITEM_PICKER2;
            else
                emulatorMenu[i].Type = MENUITEM_DISABLED;
            break;
        }
    }
    for (int i = 1; i <= 8; i++)
        optionsForDisk[i].Type = (fdsDiskNo >= i) ? MENUITEM_ACTION : MENUITEM_DISABLED;


	//svcSleepThread((long)10000000000);

	return true;
}


//---------------------------------------------------------
// This is called to determine what the frame rate of the
// game based on the ROM's region.
//---------------------------------------------------------
int impl3dsGetROMFrameRate()
{
	if (nes)
		return nes->nescfg->FrameRate;
	return 60;
}



//---------------------------------------------------------
// This is called when the user chooses to reset the
// console
//---------------------------------------------------------
void impl3dsResetConsole()
{	
	if (nes)
		nes->SoftReset();
}


//---------------------------------------------------------
// This is called when preparing to start emulating
// a new frame. Use this to do any preparation of data,
// the hardware, swap any vertex list buffers, etc, 
// before the frame is emulated
//---------------------------------------------------------
void impl3dsPrepareForNewFrame()
{
	gpu3dsSwapVertexListForNextFrame(&GPU3DSExt.quadVertexes);
    gpu3dsSwapVertexListForNextFrame(&GPU3DSExt.tileVertexes);
    gpu3dsSwapVertexListForNextFrame(&GPU3DSExt.rectangleVertexes);

    video3dsStartNewSoftwareRenderedFrame();
}




bool isOddFrame = false;
bool skipDrawingPreviousFrame = true;

uint32 			*bufferToTransfer = 0;
SGPUTexture 	*screenTexture = 0;


//---------------------------------------------------------
// Initialize any variables or state of the GPU
void impl3dsEmulationBegin()
{
	bufferToTransfer = 0;
	screenTexture = 0;
	skipDrawingPreviousFrame = true;

	gpu3dsUseShader(0);
	gpu3dsDisableAlphaBlending();
	gpu3dsDisableDepthTest();
	gpu3dsDisableAlphaTest();
	gpu3dsDisableStencilTest();
	gpu3dsSetTextureEnvironmentReplaceTexture0();
	gpu3dsSetRenderTargetToTopFrameBuffer();
	gpu3dsFlush();	
}

u32 insertCoin1 = 0;
u32 insertCoin2 = 0;

void impl3dsEmulationPollInput()
{
    u32 keysHeld3ds =
        input3dsGetCurrentKeysHeld();

    u32 consoleJoyPad =
        input3dsProcess3dsKeys();

    if (mpHostActive)
    {
        mpInitializeLockstep();

        u8 player1 =
            (u8)(consoleJoyPad & 0xFF);

        u16 synchronizedInput = 0;

        if (!mpLockstepHostGetSync(
                mpLockstepFrame,
                player1,
                &synchronizedInput))
        {
            impl3dsLocalPlayStop();

            consoleJoyPad = player1;
        }
        else
        {
            consoleJoyPad =
                synchronizedInput;

            mpLockstepFrame++;
        }
    }
    else if (mpClientActive)
    {
        mpInitializeLockstep();

        u8 player2 =
            mpMap3dsToNes(keysHeld3ds);

        u16 synchronizedInput = 0;

        if (!mpLockstepClientGetSync(
                mpLockstepFrame,
                player2,
                &synchronizedInput))
        {
            impl3dsLocalPlayStop();
        }
        else
        {
            consoleJoyPad =
                synchronizedInput;

            mpLockstepFrame++;
        }
    }

    if (nes)
        nes->pad->SetSyncData(consoleJoyPad);

    if (settings3DS.UseGlobalEmuControlKeys)
    {
        insertCoin1 =
            (keysHeld3ds &
             settings3DS.OtherOptions[
                 SETTINGS_GLOBALINSERTCOIN1
             ]) > 0;

        insertCoin2 =
            (keysHeld3ds &
             settings3DS.OtherOptions[
                 SETTINGS_GLOBALINSERTCOIN2
             ]) > 0;
    }
    else
    {
        insertCoin1 =
            (keysHeld3ds &
             settings3DS.OtherOptions[
                 SETTINGS_INSERTCOIN1
             ]) > 0;

        insertCoin2 =
            (keysHeld3ds &
             settings3DS.OtherOptions[
                 SETTINGS_INSERTCOIN2
             ]) > 0;
    }
}


//---------------------------------------------------------
// The following pipeline is used if the 
// emulation engine does software rendering.
//
// You can potentially 'hide' the wait latencies by
// waiting only after some work on the main thread
// is complete.
//---------------------------------------------------------

int lastWait = 0;
#define WAIT_PPF		1
#define WAIT_P3D		2


void impl3dsRenderDrawTextureToFrameBuffer()
{
	t3dsStartTiming(14, "Draw Texture");	

    // Draw a black colored rectangle covering the entire screen.
    //
	switch (settings3DS.ScreenStretch)
	{
		case 0:
            gpu3dsSetTextureEnvironmentReplaceColor();
            gpu3dsDrawRectangle(0, 0, 72, 240, 0, 0x000000ff);
            gpu3dsDrawRectangle(328, 0, 400, 240, 0, 0x000000ff);

            gpu3dsSetTextureEnvironmentReplaceTexture0();
            gpu3dsBindTextureMainScreen(video3dsGetPreviousScreenTexture(), GPU_TEXUNIT0);
			gpu3dsAddQuadVertexes(72, 0, 328, 240, 8, 0, 264, 240, 0);
			break;
		case 1:
            gpu3dsSetTextureEnvironmentReplaceColor();
            gpu3dsDrawRectangle(0, 0, 40, 240, 0, 0x000000ff);
            gpu3dsDrawRectangle(360, 0, 400, 240, 0, 0x000000ff);

            gpu3dsSetTextureEnvironmentReplaceTexture0();
            gpu3dsBindTextureMainScreen(video3dsGetPreviousScreenTexture(), GPU_TEXUNIT0);
			gpu3dsAddQuadVertexes(40, 0, 360, 240, 8.2, 0, 263.8, 240, 0);
			break;
		case 2:
            gpu3dsSetTextureEnvironmentReplaceTexture0();
            gpu3dsBindTextureMainScreen(video3dsGetPreviousScreenTexture(), GPU_TEXUNIT0);
			gpu3dsAddQuadVertexes(0, 0, 400, 240, 8.2, 0, 263.8, 240, 0);
			break;
		case 3:
            gpu3dsSetTextureEnvironmentReplaceColor();
            gpu3dsDrawRectangle(0, 0, 40, 240, 0, 0x000000ff);
            gpu3dsDrawRectangle(360, 0, 400, 240, 0, 0x000000ff);

            gpu3dsSetTextureEnvironmentReplaceTexture0();
            gpu3dsBindTextureMainScreen(video3dsGetPreviousScreenTexture(), GPU_TEXUNIT0);
			gpu3dsAddQuadVertexes(40, 0, 360, 240, 8.2 + 8, 0 + 8, 263.8 - 8, 240 - 8, 0);
			break;
		case 4:
            gpu3dsSetTextureEnvironmentReplaceTexture0();
            gpu3dsBindTextureMainScreen(video3dsGetPreviousScreenTexture(), GPU_TEXUNIT0);
			gpu3dsAddQuadVertexes(0, 0, 400, 240, 8.2 + 8, 0 + 8, 263.8 - 8, 240 - 8, 0);
			break;
	}
    gpu3dsDrawVertexes();
	t3dsEndTiming(14);

	t3dsStartTiming(15, "Flush");
	gpu3dsFlush();
	t3dsEndTiming(15);
}


//---------------------------------------------------------
// Executes one frame and draw to the screen.
//
// Note: TRUE will be passed in the firstFrame if this
// frame is to be run just after the emulator has booted
// up or returned from the menu.
//---------------------------------------------------------
extern int frameCount60;
void impl3dsEmulationRunOneFrame(bool firstFrame, bool skipDrawingFrame)
{
	t3dsStartTiming(1, "RunOneFrame");

#ifndef EMU_RELEASE
if (frameCount60 == 59)
{
    printf ("control1: %d\n", nes->rom->GetNesHeader()->control1);
    printf ("Mapper  : %d\n", nes->rom->GetMapperNo());
    printf ("PROM CRC: %08X\n", nes->rom->GetPROM_CRC());
    printf ("CRC     : %08X\n", nes->rom->GetROM_CRC());
}
#endif

	if (!skipDrawingPreviousFrame)
        video3dsTransferFrameBufferToScreenAndSwap();

	t3dsStartTiming(10, "EmulateFrame");
	if (nes)
	{
		impl3dsEmulationPollInput();

		if (skipDrawingFrame)
		{
			nes->EmulateFrame(false);
		}
		else
		{
            nes->ppu->SetScreenRGBAPtr( video3dsGetCurrentSoftwareBuffer(), linecolor );
			nes->EmulateFrame(true);
		}
	}
	t3dsEndTiming(10);

	if (!skipDrawingFrame)
        video3dsCopySoftwareBufferToTexture();

	if (!skipDrawingPreviousFrame)
		impl3dsRenderDrawTextureToFrameBuffer();	

	skipDrawingPreviousFrame = skipDrawingFrame;
	t3dsEndTiming(1);

}


//---------------------------------------------------------
// Finalize any variables or state of the GPU
// before the emulation loop ends and control 
// goes into the menu.
//---------------------------------------------------------
void impl3dsEmulationEnd()
{
	// We have to do this to clear the wait event
	//
	/*if (lastWait != 0 && emulator.isReal3DS)
	{
		if (lastWait == WAIT_PPF)
			gspWaitForPPF();
		else 
		if (lastWait == WAIT_P3D)
			gpu3dsWaitForPreviousFlush();
	}*/
}



//---------------------------------------------------------
// This is called when the bottom screen is touched
// during emulation, and the emulation engine is ready
// to display the pause menu.
//
// Use this to save the SRAM to SD card, if applicable.
//---------------------------------------------------------
void impl3dsEmulationPaused()
{
    if (nes)
    {
        ui3dsDrawRect(50, 140, 270, 154, 0x000000);
        ui3dsDrawStringWithNoWrapping(50, 140, 270, 154, 0x3f7fff, HALIGN_CENTER, "Saving SRAM to SD card...");
        
        nes->SaveSRAM();
    }
}


//---------------------------------------------------------
// This is called when the user chooses to save the state.
// This function should save the state into a file whose
// name contains the slot number. This will return
// true if the state is saved successfully.
//
// The slotNumbers passed in start from 1.
//---------------------------------------------------------
bool impl3dsSaveState(int slotNumber)
{
	char ext[_MAX_PATH];
    if (slotNumber == 0)
	    sprintf(ext, ".sta");
    else
	    sprintf(ext, ".st%d", slotNumber - 1);

	if (nes)
	{
		nes->SaveState(file3dsReplaceFilenameExtension(romFileNameFullPath, ext));
		return true;
	}
	else
		return false;
}


//---------------------------------------------------------
// This is called when the user chooses to load the state.
// This function should save the state into a file whose
// name contains the slot number. This will return
// true if the state is loaded successfully.
//
// The slotNumbers passed in start from 1.
//---------------------------------------------------------
bool impl3dsLoadState(int slotNumber)
{
	char ext[_MAX_PATH];
    if (slotNumber == 0)
	    sprintf(ext, ".sta");
    else
	    sprintf(ext, ".st%d", slotNumber - 1);
    
	if (nes)
	{
		nes->LoadState(file3dsReplaceFilenameExtension(romFileNameFullPath, ext));
		return true;
	}
	else
		return false;
}


//---------------------------------------------------------
// This function will be called everytime the user
// selects an action on the menu.
//
// Returns true if the menu should close and the game 
// should resume
//---------------------------------------------------------
bool impl3dsOnMenuSelected(int ID)
{
    return false;
}



//---------------------------------------------------------
// This function will be called everytime the user 
// changes the value in the specified menu item.
//
// Returns true if the menu should close and the game 
// should resume
//---------------------------------------------------------
bool impl3dsOnMenuSelectedChanged(int ID, int value)
{
    if (ID == 18000)
    {
        ui3dsSetFont(value);
        return false;
    }
    if (ID == 30000)
    {
        switch (value)
        {
            case 0:
                if( nes->rom->GetDiskNo() > 0 ) 
                    nes->Command( NES::NESCMD_DISK_EJECT );
                return true;
                break;
            case 1:
                if( nes->rom->GetDiskNo() > 0 )
                    nes->Command( NES::NESCMD_DISK_0A );
                return true;
                break;
            case 2:
                if( nes->rom->GetDiskNo() > 1 )
                    nes->Command( NES::NESCMD_DISK_0B );
                return true;
                break;
            case 3:
                if( nes->rom->GetDiskNo() > 2 )
                    nes->Command( NES::NESCMD_DISK_1A );
                return true;
                break;
            case 4:
                if( nes->rom->GetDiskNo() > 3 )
                    nes->Command( NES::NESCMD_DISK_1B );
                return true;
                break;
            case 5:
                if( nes->rom->GetDiskNo() > 4 )
                    nes->Command( NES::NESCMD_DISK_2A );
                return true;
                break;
            case 6:
                if( nes->rom->GetDiskNo() > 5 )
                    nes->Command( NES::NESCMD_DISK_2B );
                return true;
                break;
            case 7:
                if( nes->rom->GetDiskNo() > 6 )
                    nes->Command( NES::NESCMD_DISK_3A );
                return true;
                break;
            case 8:
                if( nes->rom->GetDiskNo() > 7 )
                    nes->Command( NES::NESCMD_DISK_3B );
                return true;
                break;
        }
    }
    return false;
}


//---------------------------------------------------------
// Initializes the default global settings. 
// This method is called everytime if the global settings
// file does not exist.
//---------------------------------------------------------
void impl3dsInitializeDefaultSettingsGlobal()
{
	settings3DS.GlobalVolume = 4;
	settings3DS.OtherOptions[SETTINGS_GLOBALINSERTCOIN1] = 0;	
	settings3DS.OtherOptions[SETTINGS_GLOBALINSERTCOIN2] = 0;	
}

//---------------------------------------------------------
// Initializes the default game-specific
// settings. This method is called everytime a game is
// loaded, but the configuration file does not exist.
//---------------------------------------------------------
void impl3dsInitializeDefaultSettingsByGame()
{
	settings3DS.MaxFrameSkips = 1;
	settings3DS.ForceFrameRate = 0;
	settings3DS.Volume = 4;

	settings3DS.OtherOptions[SETTINGS_INSERTCOIN1] = 0;	
	settings3DS.OtherOptions[SETTINGS_INSERTCOIN2] = 0;	
}




//----------------------------------------------------------------------
// Read/write all possible game specific settings into a file 
// created in this method.
//
// This must return true if the settings file exist.
//----------------------------------------------------------------------
bool impl3dsReadWriteSettingsByGame(bool writeMode)
{
    bool success = config3dsOpenFile(file3dsReplaceFilenameExtension(romFileNameFullPath, ".cfg"), writeMode);
    if (!success)
        return false;

    config3dsReadWriteInt32("#v1\n", NULL, 0, 0);
    config3dsReadWriteInt32("# Do not modify this file or risk losing your settings.\n", NULL, 0, 0);

    // set default values first.
    if (!writeMode)
    {
        settings3DS.PaletteFix = 0;
        settings3DS.SRAMSaveInterval = 0;
    }

    int deprecated = 0;
    config3dsReadWriteInt32("Frameskips=%d\n", &settings3DS.MaxFrameSkips, 0, 4);
    config3dsReadWriteInt32("Framerate=%d\n", &settings3DS.ForceFrameRate, 0, 2);
    config3dsReadWriteInt32("TurboA=%d\n", &settings3DS.Turbo[0], 0, 10);
    config3dsReadWriteInt32("TurboB=%d\n", &settings3DS.Turbo[1], 0, 10);
    config3dsReadWriteInt32("TurboX=%d\n", &settings3DS.Turbo[2], 0, 10);
    config3dsReadWriteInt32("TurboY=%d\n", &settings3DS.Turbo[3], 0, 10);
    config3dsReadWriteInt32("TurboL=%d\n", &settings3DS.Turbo[4], 0, 10);
    config3dsReadWriteInt32("TurboR=%d\n", &settings3DS.Turbo[5], 0, 10);
    config3dsReadWriteInt32("Vol=%d\n", &settings3DS.Volume, 0, 8);
    config3dsReadWriteInt32("SRAMInterval=%d\n", &settings3DS.SRAMSaveInterval, 0, 4);
    config3dsReadWriteInt32("ButtonMapA=%d\n", &deprecated, 0, 0xffff);
    config3dsReadWriteInt32("ButtonMapB=%d\n", &deprecated, 0, 0xffff);
    config3dsReadWriteInt32("ButtonMapX=%d\n", &deprecated, 0, 0xffff);
    config3dsReadWriteInt32("ButtonMapY=%d\n", &deprecated, 0, 0xffff);
    config3dsReadWriteInt32("ButtonMapL=%d\n", &deprecated, 0, 0xffff);
    config3dsReadWriteInt32("ButtonMapR=%d\n", &deprecated, 0, 0xffff);
    config3dsReadWriteInt32("AllSprites=%d\n", &settings3DS.OtherOptions[SETTINGS_ALLSPRITES], 0, 1);

    // v1.00 options
    //
    config3dsReadWriteInt32("TurboZL=%d\n", &settings3DS.Turbo[6], 0, 10);
    config3dsReadWriteInt32("TurboZR=%d\n", &settings3DS.Turbo[7], 0, 10);
    static char *buttonName[10] = {"A", "B", "X", "Y", "L", "R", "ZL", "ZR", "SELECT","START"};
    char buttonNameFormat[50];
    for (int i = 0; i < 10; ++i) {
        for (int j = 0; j < 2; ++j) {
            sprintf(buttonNameFormat, "ButtonMap%s_%d=%%d\n", buttonName[i], j);
            config3dsReadWriteInt32(buttonNameFormat, &settings3DS.ButtonMapping[i][j]);
        }
    }
    config3dsReadWriteInt32("ButtonMappingDisableFramelimitHold=%d\n", &settings3DS.ButtonHotkeyDisableFramelimit);
    config3dsReadWriteInt32("ButtonMappingOpenEmulatorMenu=%d\n", &settings3DS.ButtonHotkeyOpenMenu);
    config3dsReadWriteInt32("ButtonMappingInsertCoin1=%d\n", &settings3DS.OtherOptions[SETTINGS_INSERTCOIN1]);
    config3dsReadWriteInt32("ButtonMappingInsertCoin2=%d\n", &settings3DS.OtherOptions[SETTINGS_INSERTCOIN2]);
    config3dsReadWriteInt32("PalFix=%d\n", &settings3DS.PaletteFix, 0, 1);

    // All new options should come here!

    config3dsCloseFile();
    return true;
}


//----------------------------------------------------------------------
// Read/write all possible global specific settings into a file 
// created in this method.
//
// This must return true if the settings file exist.
//----------------------------------------------------------------------
bool impl3dsReadWriteSettingsGlobal(bool writeMode)
{
    bool success = config3dsOpenFile("./virtuanes_3ds.cfg", writeMode);
    if (!success)
        return false;
    
    int deprecated = 0;

    config3dsReadWriteInt32("#v1\n", NULL, 0, 0);
    config3dsReadWriteInt32("# Do not modify this file or risk losing your settings.\n", NULL, 0, 0);

    config3dsReadWriteInt32("ScreenStretch=%d\n", &settings3DS.ScreenStretch, 0, 7);
    config3dsReadWriteInt32("HideUnnecessaryBottomScrText=%d\n", &settings3DS.HideUnnecessaryBottomScrText, 0, 1);
    config3dsReadWriteInt32("Font=%d\n", &settings3DS.Font, 0, 2);
    config3dsReadWriteInt32("UseGlobalButtonMappings=%d\n", &settings3DS.UseGlobalButtonMappings, 0, 1);
    config3dsReadWriteInt32("UseGlobalTurbo=%d\n", &settings3DS.UseGlobalTurbo, 0, 1);
    config3dsReadWriteInt32("UseGlobalVolume=%d\n", &settings3DS.UseGlobalVolume, 0, 1);
    config3dsReadWriteInt32("TurboA=%d\n", &settings3DS.GlobalTurbo[0], 0, 10);
    config3dsReadWriteInt32("TurboB=%d\n", &settings3DS.GlobalTurbo[1], 0, 10);
    config3dsReadWriteInt32("TurboX=%d\n", &settings3DS.GlobalTurbo[2], 0, 10);
    config3dsReadWriteInt32("TurboY=%d\n", &settings3DS.GlobalTurbo[3], 0, 10);
    config3dsReadWriteInt32("TurboL=%d\n", &settings3DS.GlobalTurbo[4], 0, 10);
    config3dsReadWriteInt32("TurboR=%d\n", &settings3DS.GlobalTurbo[5], 0, 10);
    config3dsReadWriteInt32("Vol=%d\n", &settings3DS.GlobalVolume, 0, 8);
    config3dsReadWriteInt32("ButtonMapA=%d\n", &deprecated, 0, 0xffff);
    config3dsReadWriteInt32("ButtonMapB=%d\n", &deprecated, 0, 0xffff);
    config3dsReadWriteInt32("ButtonMapX=%d\n", &deprecated, 0, 0xffff);
    config3dsReadWriteInt32("ButtonMapY=%d\n", &deprecated, 0, 0xffff);
    config3dsReadWriteInt32("ButtonMapL=%d\n", &deprecated, 0, 0xffff);
    config3dsReadWriteInt32("ButtonMapR=%d\n", &deprecated, 0, 0xffff);

    // Fixes the bug where we have spaces in the directory name
    config3dsReadWriteString("Dir=%s\n", "Dir=%1000[^\n]s\n", file3dsGetCurrentDir());
    config3dsReadWriteString("ROM=%s\n", "ROM=%1000[^\n]s\n", romFileNameLastSelected);

    // v1.00 options
    //
    config3dsReadWriteInt32("AutoSavestate=%d\n", &settings3DS.AutoSavestate, 0, 1);
    config3dsReadWriteInt32("TurboZL=%d\n", &settings3DS.GlobalTurbo[6], 0, 10);
    config3dsReadWriteInt32("TurboZR=%d\n", &settings3DS.GlobalTurbo[7], 0, 10);
    static char *buttonName[10] = {"A", "B", "X", "Y", "L", "R", "ZL", "ZR", "SELECT","START"};
    char buttonNameFormat[50];
    for (int i = 0; i < 10; ++i) {
        for (int j = 0; j < 2; ++j) {
            sprintf(buttonNameFormat, "ButtonMap%s_%d=%%d\n", buttonName[i], j);
            config3dsReadWriteInt32(buttonNameFormat, &settings3DS.GlobalButtonMapping[i][j]);
        }
    }
    config3dsReadWriteInt32("UseGlobalEmuControlKeys=%d\n", &settings3DS.UseGlobalEmuControlKeys, 0, 1);
    config3dsReadWriteInt32("ButtonMappingDisableFramelimitHold_0=%d\n", &settings3DS.GlobalButtonHotkeyDisableFramelimit);
    config3dsReadWriteInt32("ButtonMappingOpenEmulatorMenu_0=%d\n", &settings3DS.GlobalButtonHotkeyOpenMenu);
    config3dsReadWriteInt32("ButtonMappingInsertCoin1=%d\n", &settings3DS.OtherOptions[SETTINGS_GLOBALINSERTCOIN1]);
    config3dsReadWriteInt32("ButtonMappingInsertCoin2=%d\n", &settings3DS.OtherOptions[SETTINGS_GLOBALINSERTCOIN2]);

    // All new options should come here!

    config3dsCloseFile();
    return true;
}



//----------------------------------------------------------------------
// Apply settings into the emulator.
//
// This method normally copies settings from the settings3DS struct
// and updates the emulator's core's configuration.
//
// This must return true if any settings were modified.
//----------------------------------------------------------------------
bool impl3dsApplyAllSettings(bool updateGameSettings)
{
    bool settingsChanged = false;

    // update screen stretch
    //
    if (settings3DS.ScreenStretch == 0)
    {
        settings3DS.StretchWidth = 256;
        settings3DS.StretchHeight = 240;    // Actual height
        settings3DS.CropPixels = 0;
    }
    else if (settings3DS.ScreenStretch == 1)
    {
        // Added support for 320x240 (4:3) screen ratio
        settings3DS.StretchWidth = 320;
        settings3DS.StretchHeight = 240;
        settings3DS.CropPixels = 0;
    }
    else if (settings3DS.ScreenStretch == 2)
    {
        settings3DS.StretchWidth = 400;
        settings3DS.StretchHeight = 240;
        settings3DS.CropPixels = 0;
    }

    // Update the screen font
    //
    ui3dsSetFont(settings3DS.Font);

    // update global volume
    //
    if (settings3DS.Volume < 0)
        settings3DS.Volume = 0;
    if (settings3DS.Volume > 8)
        settings3DS.Volume = 8;
    if (settings3DS.GlobalVolume < 0)
        settings3DS.GlobalVolume = 0;
    if (settings3DS.GlobalVolume > 8)
        settings3DS.GlobalVolume = 8;
    
    int vol[9] = { 100, 125, 150, 175, 200, 250, 300, 350, 400 };
    Config.sound.nVolume[0] = vol[settings3DS.Volume];
    if (settings3DS.UseGlobalVolume)
        Config.sound.nVolume[0] = vol[settings3DS.GlobalVolume];

    if (updateGameSettings)
    {
        if (settings3DS.ForceFrameRate == 0)
            settings3DS.TicksPerFrame = TICKS_PER_SEC / impl3dsGetROMFrameRate();

        if (settings3DS.ForceFrameRate == 1)
            settings3DS.TicksPerFrame = TICKS_PER_FRAME_PAL;

        else if (settings3DS.ForceFrameRate == 2)
            settings3DS.TicksPerFrame = TICKS_PER_FRAME_NTSC;

        Config.graphics.bAllSprite = settings3DS.OtherOptions[SETTINGS_ALLSPRITES];
    }

    return settingsChanged;
}


//----------------------------------------------------------------------
// Copy values from menu to settings3DS structure,
// or from settings3DS structure to the menu, depending on the
// copyMenuToSettings parameter.
//
// This must return return if any of the settings were changed.
//----------------------------------------------------------------------
bool impl3dsCopyMenuToOrFromSettings(bool copyMenuToSettings)
{
#define UPDATE_SETTINGS(var, tabIndex, ID)  \
    { \
    if (copyMenuToSettings && (var) != menu3dsGetValueByID(tabIndex, ID)) \
    { \
        var = menu3dsGetValueByID(tabIndex, (ID)); \
        settingsUpdated = true; \
    } \
    if (!copyMenuToSettings) \
    { \
        menu3dsSetValueByID(tabIndex, (ID), (var)); \
    } \
    }

    bool settingsUpdated = false;
    UPDATE_SETTINGS(settings3DS.Font, -1, 18000);
    UPDATE_SETTINGS(settings3DS.ScreenStretch, -1, 11000);
    UPDATE_SETTINGS(settings3DS.HideUnnecessaryBottomScrText, -1, 15001);
    UPDATE_SETTINGS(settings3DS.MaxFrameSkips, -1, 10000);
    UPDATE_SETTINGS(settings3DS.ForceFrameRate, -1, 12000);
    UPDATE_SETTINGS(settings3DS.UseGlobalButtonMappings, -1, 20000);
    UPDATE_SETTINGS(settings3DS.UseGlobalTurbo, -1, 20001);
    UPDATE_SETTINGS(settings3DS.UseGlobalVolume, -1, 20002);
    UPDATE_SETTINGS(settings3DS.AutoSavestate, -1, 21000);

    UPDATE_SETTINGS(settings3DS.UseGlobalEmuControlKeys, -1, 50003);
    if (settings3DS.UseGlobalButtonMappings || copyMenuToSettings)
    {
        for (int i = 0; i < 2; i++)
            for (int b = 0; b < 10; b++)
                UPDATE_SETTINGS(settings3DS.GlobalButtonMapping[b][i], -1, 13010 + b + (i * 10));
    }
    if (!settings3DS.UseGlobalButtonMappings || copyMenuToSettings)
    {
        for (int i = 0; i < 2; i++)
            for (int b = 0; b < 10; b++)
                UPDATE_SETTINGS(settings3DS.ButtonMapping[b][i], -1, 13010 + b + (i * 10));
    }
    if (settings3DS.UseGlobalTurbo || copyMenuToSettings)
    {
        for (int b = 0; b < 8; b++)
            UPDATE_SETTINGS(settings3DS.GlobalTurbo[b], -1, 13000 + b);
    }
    if (!settings3DS.UseGlobalTurbo || copyMenuToSettings) 
    {
        for (int b = 0; b < 8; b++)
            UPDATE_SETTINGS(settings3DS.Turbo[b], -1, 13000 + b);
    }
    if (settings3DS.UseGlobalVolume || copyMenuToSettings)
    {
        UPDATE_SETTINGS(settings3DS.GlobalVolume, -1, 14000);
    }
    if (!settings3DS.UseGlobalVolume || copyMenuToSettings)
    {
        UPDATE_SETTINGS(settings3DS.Volume, -1, 14000);
    }
    if (settings3DS.UseGlobalEmuControlKeys || copyMenuToSettings)
    {
        UPDATE_SETTINGS(settings3DS.GlobalButtonHotkeyOpenMenu, -1, 23001);
        UPDATE_SETTINGS(settings3DS.GlobalButtonHotkeyDisableFramelimit, -1, 23002);
        UPDATE_SETTINGS(settings3DS.OtherOptions[SETTINGS_GLOBALINSERTCOIN1], -1, 23003);
        UPDATE_SETTINGS(settings3DS.OtherOptions[SETTINGS_GLOBALINSERTCOIN2], -1, 23004);
    }
    if (!settings3DS.UseGlobalEmuControlKeys || copyMenuToSettings)
    {
        UPDATE_SETTINGS(settings3DS.ButtonHotkeyOpenMenu, -1, 23001);
        UPDATE_SETTINGS(settings3DS.ButtonHotkeyDisableFramelimit, -1, 23002);
        UPDATE_SETTINGS(settings3DS.OtherOptions[SETTINGS_INSERTCOIN1], -1, 23003);
        UPDATE_SETTINGS(settings3DS.OtherOptions[SETTINGS_INSERTCOIN1], -1, 23004);
    }
    
    UPDATE_SETTINGS(settings3DS.OtherOptions[SETTINGS_ALLSPRITES], -1, 19000);     // sprite flicker

    return settingsUpdated;
	
}



//----------------------------------------------------------------------
// Clears all cheats from the core.
//
// This method is called only when cheats are loaded.
// This only happens after a new ROM is loaded.
//----------------------------------------------------------------------
void impl3dsClearAllCheats()
{
    if (nes)
        nes->GenieInitial();
}


//----------------------------------------------------------------------
// Adds cheats into the emulator core after being loaded up from 
// the .CHX file.
//
// This method is called only when cheats are loaded.
// This only happens after a new ROM is loaded.
//
// This method must return true if the cheat code format is valid,
// and the cheat is added successfully into the core.
//----------------------------------------------------------------------
bool impl3dsAddCheat(bool cheatEnabled, char *name, char *code)
{
    return nes->GenieAdd(cheatEnabled, code);    
}


//----------------------------------------------------------------------
// Enable/disables a cheat in the emulator core.
// 
// This method will be triggered when the user enables/disables
// cheats in the cheat menu.
//----------------------------------------------------------------------
void impl3dsSetCheatEnabledFlag(int cheatIdx, bool enabled)
{
    nes->GenieSet(cheatIdx, enabled);
}
