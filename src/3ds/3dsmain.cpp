#include <algorithm>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <ctime>
#include <vector>

#include <unistd.h>
#include <string.h>
#include <stdio.h>
#include <3ds.h>

#include <dirent.h>

#include "3dstypes.h"
#include "3dsexit.h"
#include "3dsgpu.h"
#include "3dsopt.h"
#include "3dssound.h"
#include "3dsmenu.h"
#include "3dsui.h"
#include "3dsfont.h"
#include "3dsconfig.h"
#include "3dsfiles.h"
#include "3dsinput.h"
#include "3dslodepng.h"
#include "3dsmenu.h"
#include "3dsmain.h"
#include "3dsdbg.h"

#include "3dsinterface.h"
#include "3dscheat.h"


SEmulator emulator;

int frameCount60 = 60;
u64 frameCountTick = 0;
int framesSkippedCount = 0;
char *romFileName = 0;
char romFileNameFullPath[_MAX_PATH];
char romFileNameLastSelected[_MAX_PATH];

void clearTopScreenWithLogo()
{
	unsigned char* image;
	unsigned width, height;

    int error = lodepng_decode32_file(&image, &width, &height, impl3dsTitleImage);

    if (!error && width == 400 && height == 240)
    {
        for (int i = 0; i < 2; i++)
        {
            u8* src = image;
            uint32* fb = (uint32 *) gfxGetFramebuffer(GFX_TOP, GFX_LEFT, NULL, NULL);
            for (int y = 0; y < 240; y++)
                for (int x = 0; x < 400; x++)
                {
                    uint32 r = *src++;
                    uint32 g = *src++;
                    uint32 b = *src++;
                    uint32 a = *src++;

                    uint32 c = ((r << 24) | (g << 16) | (b << 8) | 0xff);
                    fb[x * 240 + (239 - y)] = c;
                }
            gfxSwapBuffers();
        }

        free(image);
    }
}
SMenuItem emulatorNewMenu[] = {
    MENU_MAKE_ACTION(6001, "  Exit"),
    MENU_MAKE_LASTITEM  ()
    };

enum LocalPlayMode
{
    LOCALPLAY_SINGLE = 0,
    LOCALPLAY_HOST,
    LOCALPLAY_JOIN
};

static LocalPlayMode localPlayMode = LOCALPLAY_SINGLE;
static bool hostLobbyActive = false;
static bool joinLobbyActive = false;
static bool joinDiscoveryActive = false;

static bool hostStartRequested = false;
static bool hostCorePrepared = false;
static bool joinCorePrepared = false;
static bool localPlayLaunchPending = false;
static bool joinLobbyHostConnected = false;

SMenuItem localPlayMenu[] = {
    MENU_MAKE_ACTION(6101, "[X] Single"),
    MENU_MAKE_ACTION(6102, "[ ] Host"),
    MENU_MAKE_ACTION(6103, "[ ] Join"),
    MENU_MAKE_LASTITEM()
};

static char hostLobbyGameText[_MAX_PATH] = "Game: ";
static char hostLobbyPlayer2Text[128] =
    "Player 2: Waiting...";

SMenuItem hostLobbyMenu[] = {
    MENU_MAKE_HEADER1("Local Play - Host"),
    MENU_MAKE_DISABLED(hostLobbyGameText),
    MENU_MAKE_DISABLED("Player 1: Ready"),
    MENU_MAKE_DISABLED(hostLobbyPlayer2Text),
    MENU_MAKE_DISABLED("  Start Game"),
    MENU_MAKE_LASTITEM()
};

static char joinLobbyHostText[64] = "Joined: Host";
static char joinLobbyGameText[128] = "Game: Unknown";
static char joinLobbyStatusText[96] = "Waiting for ROM info...";

SMenuItem joinLobbyMenu[] = {
    MENU_MAKE_HEADER1("Local Play - Join"),
    MENU_MAKE_DISABLED(joinLobbyHostText),
    MENU_MAKE_DISABLED(joinLobbyGameText),
    MENU_MAKE_DISABLED(joinLobbyStatusText),
    MENU_MAKE_LASTITEM()
};

#define LOCALPLAY_MAX_LOBBIES 8

static char nearbyHostNames[LOCALPLAY_MAX_LOBBIES][32];
static char nearbyGameNames[LOCALPLAY_MAX_LOBBIES][96];
static char nearbyGameRows[LOCALPLAY_MAX_LOBBIES][140];

static SMenuItem nearbyGamesMenu[LOCALPLAY_MAX_LOBBIES + 2];
static int nearbyGameCount = 0;


static void buildNearbyGamesMenu()
{
    memset(nearbyGamesMenu, 0, sizeof(nearbyGamesMenu));

    nearbyGamesMenu[0].Type = MENUITEM_HEADER1;
    nearbyGamesMenu[0].ID = -1;
    nearbyGamesMenu[0].Text = (char *)"Nearby Games";

    for (int i = 0; i < nearbyGameCount; i++)
    {
        snprintf(
            nearbyGameRows[i],
            sizeof(nearbyGameRows[i]),
            "%-10s  %s",
            nearbyHostNames[i],
            nearbyGameNames[i]
        );

        nearbyGamesMenu[i + 1].Type = MENUITEM_ACTION;
        nearbyGamesMenu[i + 1].ID = 6300 + i;
        nearbyGamesMenu[i + 1].Text = nearbyGameRows[i];
        nearbyGamesMenu[i + 1].Description = NULL;
    }

    nearbyGamesMenu[nearbyGameCount + 1].Type =
        MENUITEM_LASTITEM;
}


bool impl3dsLocalPlayHasGuest();
bool impl3dsLocalPlayClientHasHost();

bool impl3dsLocalPlayHostPollTransfer(
    u32 *sentBytes,
    u32 *totalBytes,
    bool *ready,
    bool *failed);

bool impl3dsLocalPlayClientPollTransfer(
    char *gameName,
    size_t gameNameSize,
    u32 *receivedBytes,
    u32 *totalBytes,
    bool *ready,
    bool *failed);

const char *impl3dsLocalPlayGetReceivedRomPath();

bool impl3dsLocalPlayHostBeginStart();
int impl3dsLocalPlayHostPollStart();
void impl3dsLocalPlayHostSendGo();

int impl3dsLocalPlayClientPollStart();
void impl3dsLocalPlayClientMarkStartReady();

int impl3dsLocalPlayScanHosts(
    char hostNames[][32],
    char gameNames[][96],
    int maxHosts);

bool impl3dsLocalPlayJoinScannedHost(int index);

void impl3dsLocalPlayStop();

static bool hostLobbyGuestConnected = false;

static bool updateHostLobby()
{
    if (!hostLobbyActive)
        return false;

    bool redraw = false;
    bool connected = impl3dsLocalPlayHasGuest();

    u32 sentBytes = 0;
    u32 totalBytes = 0;
    bool ready = false;
    bool failed = false;

    if (impl3dsLocalPlayHostPollTransfer(
            &sentBytes,
            &totalBytes,
            &ready,
            &failed))
    {
        redraw = true;
    }

    if (connected != hostLobbyGuestConnected)
    {
        hostLobbyGuestConnected = connected;
        redraw = true;
    }

    if (!connected)
    {
        snprintf(
            hostLobbyPlayer2Text,
            sizeof(hostLobbyPlayer2Text),
            "Player 2: Waiting..."
        );
    }
    else if (failed)
    {
        snprintf(
            hostLobbyPlayer2Text,
            sizeof(hostLobbyPlayer2Text),
            "Player 2: Transfer failed"
        );
    }
    else if (ready)
    {
        snprintf(
            hostLobbyPlayer2Text,
            sizeof(hostLobbyPlayer2Text),
            "Player 2: Ready"
        );
    }
    else
    {
        snprintf(
            hostLobbyPlayer2Text,
            sizeof(hostLobbyPlayer2Text),
            "Player 2: Receiving %lu / %lu",
            (unsigned long)sentBytes,
            (unsigned long)totalBytes
        );
    }

    hostLobbyMenu[3].Text =
        hostLobbyPlayer2Text;

    if (connected &&
        ready &&
        !hostStartRequested)
    {
        if (hostLobbyMenu[4].Type !=
            MENUITEM_ACTION)
        {
            hostLobbyMenu[4].Type =
                MENUITEM_ACTION;

            hostLobbyMenu[4].ID = 6201;
            hostLobbyMenu[4].Text =
                "  Start Game";

            menu3dsSetSelectedItemIndexByID(
                0,
                6201
            );

            redraw = true;
        }
    }
    else if (!hostStartRequested)
    {
        if (hostLobbyMenu[4].Type !=
            MENUITEM_DISABLED)
        {
            hostLobbyMenu[4].Type =
                MENUITEM_DISABLED;

            hostLobbyMenu[4].ID = -1;
            hostLobbyMenu[4].Text =
                "  Start Game";

            redraw = true;
        }
    }

    if (hostStartRequested)
    {
        int startEvent =
            impl3dsLocalPlayHostPollStart();

        if (startEvent == -1)
        {
            hostStartRequested = false;
            hostCorePrepared = false;

            hostLobbyMenu[4].Type =
                MENUITEM_ACTION;

            hostLobbyMenu[4].ID = 6201;
            hostLobbyMenu[4].Text =
                "  Retry Start";

            menu3dsSetSelectedItemIndexByID(
                0,
                6201
            );

            redraw = true;
        }

        // Guest has now loaded the exact savestate that
        // System A currently has.
        if (startEvent == 1)
        {
            hostCorePrepared = true;

            hostLobbyMenu[4].Text =
                "  Starting...";

            // Do NOT reload/reset A here.
            // A's current core is the canonical state.
            impl3dsLocalPlayHostSendGo();

            redraw = true;
        }

        if (startEvent == 2 &&
            hostCorePrepared)
        {
            emulator.emulatorState =
                EMUSTATE_EMULATE;

            localPlayLaunchPending = true;

            menu3dsSetFrameCallback(NULL);
            menu3dsRequestExit();

            return true;
        }
    }

    return redraw;
}


static bool updateJoinLobby()
{
    if (!joinLobbyActive ||
        !joinLobbyHostConnected)
    {
        return false;
    }

    if (!impl3dsLocalPlayClientHasHost())
    {
        joinLobbyHostConnected = false;

        joinLobbyMenu[1].Text =
            "Disconnected from Host";

        joinLobbyMenu[2].Text =
            "Press B to return";

        joinLobbyMenu[3].Text = "";

        impl3dsLocalPlayStop();

        return true;
    }

    bool redraw = false;

    char transferGame[96] = {};
    u32 receivedBytes = 0;
    u32 totalBytes = 0;
    bool ready = false;
    bool failed = false;

    if (impl3dsLocalPlayClientPollTransfer(
            transferGame,
            sizeof(transferGame),
            &receivedBytes,
            &totalBytes,
            &ready,
            &failed))
    {
        redraw = true;
    }

    if (transferGame[0])
    {
        snprintf(
            joinLobbyGameText,
            sizeof(joinLobbyGameText),
            "Game: %s",
            transferGame
        );

        joinLobbyMenu[2].Text =
            joinLobbyGameText;
    }

    if (failed)
    {
        snprintf(
            joinLobbyStatusText,
            sizeof(joinLobbyStatusText),
            "ROM transfer failed"
        );
    }
    else if (ready && !joinCorePrepared)
    {
        snprintf(
            joinLobbyStatusText,
            sizeof(joinLobbyStatusText),
            "Ready"
        );
    }
    else if (!ready &&
             totalBytes > 0)
    {
        snprintf(
            joinLobbyStatusText,
            sizeof(joinLobbyStatusText),
            "Receiving: %lu / %lu bytes",
            (unsigned long)receivedBytes,
            (unsigned long)totalBytes
        );
    }

    joinLobbyMenu[3].Text =
        joinLobbyStatusText;

    if (ready)
    {
        int startEvent =
            impl3dsLocalPlayClientPollStart();

        if (startEvent == -1)
        {
            snprintf(
                joinLobbyStatusText,
                sizeof(joinLobbyStatusText),
                "State sync failed"
            );

            redraw = true;
        }

        // The transferred ROM and the host's canonical
        // savestate have already been loaded inside
        // impl3dsLocalPlayClientPollStart().
        if (startEvent == 1)
        {
            const char *tempRomPath =
                impl3dsLocalPlayGetReceivedRomPath();

            if (tempRomPath)
            {
                strncpy(
                    romFileNameFullPath,
                    tempRomPath,
                    _MAX_PATH - 1
                );

                romFileNameFullPath[
                    _MAX_PATH - 1
                ] = '\0';
            }

            joinCorePrepared = true;

            snprintf(
                joinLobbyStatusText,
                sizeof(joinLobbyStatusText),
                "Ready - synchronized..."
            );

            redraw = true;
        }

        if (startEvent == 2 &&
            joinCorePrepared)
        {
            emulator.emulatorState =
                EMUSTATE_EMULATE;

            localPlayLaunchPending = true;

            menu3dsSetFrameCallback(NULL);
            menu3dsRequestExit();

            return true;
        }
    }

    return redraw;
}

static void updateLocalPlayMenu()
{
    localPlayMenu[0].Text =
        localPlayMode == LOCALPLAY_SINGLE ? "[X] Single" : "[ ] Single";

    localPlayMenu[1].Text =
        localPlayMode == LOCALPLAY_HOST ? "[X] Host" : "[ ] Host";

    localPlayMenu[2].Text =
        localPlayMode == LOCALPLAY_JOIN ? "[X] Join" : "[ ] Join";
}

extern SMenuItem emulatorMenu[];
bool emulatorSettingsLoad(bool, bool, bool);
bool emulatorSettingsSave(bool, bool, bool);

bool impl3dsLocalPlayStartHost(
    const char *gameName,
    const char *romPath);
bool impl3dsLocalPlayJoinFirstHost(
    char *hostName,
    size_t hostNameSize,
    char *gameName,
    size_t gameNameSize);
bool impl3dsLocalPlayClientHasHost();
bool impl3dsLocalPlayHasGuest();
void impl3dsLocalPlayStop();

bool emulatorLoadRom()
{
    impl3dsClearAllCheats();

    menu3dsShowDialog("Load ROM", "Loading... this may take a while.", DIALOGCOLOR_CYAN, NULL);

    char romFileNameFullPathOriginal[_MAX_PATH];
    strncpy(romFileNameFullPathOriginal, romFileNameFullPath, _MAX_PATH - 1);

    snprintf(romFileNameFullPath, _MAX_PATH, "%s%s", file3dsGetCurrentDir(), romFileName);

    char romFileNameFullPath2[_MAX_PATH];
    strncpy(romFileNameFullPath2, romFileNameFullPath, _MAX_PATH - 1);

    emulatorSettingsLoad(false, true, false);
    impl3dsApplyAllSettings();
    
    if (!impl3dsLoadROM(romFileNameFullPath2))
    {
        strncpy(romFileNameFullPath, romFileNameFullPathOriginal, _MAX_PATH - 1);

        impl3dsApplyAllSettings();
        
        menu3dsHideDialog();

        return false;
    }
    impl3dsApplyAllSettings();

    if (settings3DS.AutoSavestate)
        impl3dsLoadState(0);

    emulator.emulatorState = EMUSTATE_EMULATE;

    cheat3dsLoadCheatTextFile(file3dsReplaceFilenameExtension(romFileNameFullPath, ".chx"));
    menu3dsHideDialog();

    impl3dsCopyMenuToOrFromSettings(false);

    return true;
}
#define MAX_FILES 1000
SMenuItem fileMenu[MAX_FILES + 1];
std::vector<std::string> fileList;

int totalRomFileCount = 0;
void fileGetAllFiles(void)
{
    fileList = file3dsGetFiles(impl3dsRomExtensions, MAX_FILES);

    totalRomFileCount = 0;

    for (int i = 0; i < fileList.size() && i < MAX_FILES; i++)
    {
        totalRomFileCount++;
        fileMenu[i].Type = MENUITEM_ACTION;
        fileMenu[i].ID = i;
        fileMenu[i].Text = fileList[i].c_str();
    }
    fileMenu[totalRomFileCount].Type = MENUITEM_LASTITEM;
}
int fileFindLastSelectedFile()
{
    for (int i = 0; i < totalRomFileCount && i < MAX_FILES; i++)
    {
        if (strncmp(fileMenu[i].Text, romFileNameLastSelected, _MAX_PATH) == 0)
            return i;
    }
    return -1;
}
bool emulatorSettingsLoad(bool includeGlobalSettings, bool includeGameSettings, bool showMessage = true)
{
    if (includeGlobalSettings)
    {
        bool success = impl3dsReadWriteSettingsGlobal(false);
        if (success)
        {
            input3dsSetDefaultButtonMappings(settings3DS.GlobalButtonMapping, settings3DS.GlobalTurbo, false);
            impl3dsApplyAllSettings(false);
        }
        else
        {
            impl3dsInitializeDefaultSettingsGlobal();
            input3dsSetDefaultButtonMappings(settings3DS.GlobalButtonMapping, settings3DS.GlobalTurbo, true);
            impl3dsApplyAllSettings(false);
            return false;
        }
    }

    if (includeGameSettings)
    {
        bool success = impl3dsReadWriteSettingsByGame(false);
        if (success)
        {
            input3dsSetDefaultButtonMappings(settings3DS.ButtonMapping, settings3DS.Turbo, false);
            impl3dsApplyAllSettings();
            return true;
        }
        else
        {
            impl3dsInitializeDefaultSettingsByGame();
            input3dsSetDefaultButtonMappings(settings3DS.ButtonMapping, settings3DS.Turbo, true);
            impl3dsApplyAllSettings();

            return true;
        }
    }
    return true;
}
bool emulatorSettingsSave(bool includeGlobalSettings, bool includeGameSettings, bool showMessage)
{
    if (showMessage)
    {
        consoleClear();
        ui3dsDrawRect(50, 140, 270, 154, 0x000000);
        ui3dsDrawStringWithNoWrapping(50, 140, 270, 154, 0x3f7fff, HALIGN_CENTER, "Saving settings to SD card...");
    }

    if (includeGameSettings)
    {
        impl3dsReadWriteSettingsByGame(true);
    }

    if (includeGlobalSettings)
    {
        impl3dsReadWriteSettingsGlobal(true);
    }

    if (showMessage)
    {
        ui3dsDrawRect(50, 140, 270, 154, 0x000000);
    }

    return true;
}
void menuSelectFile(void)
{
    gfxSetDoubleBuffering(GFX_BOTTOM, true);
    
    fileGetAllFiles();
    int previousFileID = fileFindLastSelectedFile();
    menu3dsClearMenuTabs();
    menu3dsAddTab("Emulator", emulatorNewMenu);
    menu3dsAddTab("Select ROM", fileMenu);
    menu3dsAddTab("Local Play", localPlayMenu);
    menu3dsSetTabSubTitle(0, NULL);
    menu3dsSetTabSubTitle(1, file3dsGetCurrentDir());
    menu3dsSetCurrentMenuTab(1);
    if (previousFileID >= 0)
        menu3dsSetSelectedItemIndexByID(1, previousFileID);
    menu3dsSetTransferGameScreen(false);

    bool animateMenu = true;
    int selection = 0;
    do
    {
        if (appExiting)
            return;

        selection = menu3dsShowMenu(NULL, animateMenu);
        animateMenu = false;

        if (selection == -2 && localPlayLaunchPending)
        {
            localPlayLaunchPending = false;

            hostLobbyActive = false;
            joinLobbyActive = false;
            joinDiscoveryActive = false;

            hostStartRequested = false;
            hostCorePrepared = false;
            joinCorePrepared = false;

            menu3dsSetFrameCallback(NULL);

            menu3dsHideMenu();
            consoleInit(GFX_BOTTOM, NULL);
            consoleClear();

            return;
        }

        if (selection == -1 && hostLobbyActive)
        {
            impl3dsLocalPlayStop();
            hostLobbyActive = false;
            hostLobbyGuestConnected = false;
            menu3dsSetFrameCallback(NULL);

            menu3dsClearMenuTabs();
            menu3dsAddTab("Emulator", emulatorNewMenu);
            menu3dsAddTab("Select ROM", fileMenu);
            menu3dsAddTab("Local Play", localPlayMenu);

            menu3dsSetTabSubTitle(0, NULL);
            menu3dsSetTabSubTitle(1, file3dsGetCurrentDir());
            menu3dsSetCurrentMenuTab(1);

            continue;
        }

        if (selection == -1 && joinDiscoveryActive)
        {
            impl3dsLocalPlayStop();
            joinDiscoveryActive = false;

            menu3dsClearMenuTabs();
            menu3dsAddTab("Emulator", emulatorNewMenu);
            menu3dsAddTab("Select ROM", fileMenu);
            menu3dsAddTab("Local Play", localPlayMenu);

            menu3dsSetTabSubTitle(0, NULL);
            menu3dsSetTabSubTitle(1, file3dsGetCurrentDir());
            menu3dsSetCurrentMenuTab(2);

            continue;
        }

        if (selection == -1 && joinLobbyActive)
        {
            impl3dsLocalPlayStop();
            joinLobbyActive = false;
            joinLobbyHostConnected = false;
            menu3dsSetFrameCallback(NULL);

            menu3dsClearMenuTabs();
            menu3dsAddTab("Emulator", emulatorNewMenu);
            menu3dsAddTab("Select ROM", fileMenu);
            menu3dsAddTab("Local Play", localPlayMenu);

            menu3dsSetTabSubTitle(0, NULL);
            menu3dsSetTabSubTitle(1, file3dsGetCurrentDir());
            menu3dsSetCurrentMenuTab(2);

            continue;
        }

        if (selection >= 0 && selection < 1000)
        {
            romFileName = fileList[selection].c_str();
            strncpy(romFileNameLastSelected, romFileName, _MAX_PATH);
            if (romFileName[0] == 1)
            {
                if (strcmp(romFileName, "\x01 ..") == 0)
                    file3dsGoToParentDirectory();
                else
                    file3dsGoToChildDirectory(&romFileName[2]);

                fileGetAllFiles();
                menu3dsClearMenuTabs();
                menu3dsAddTab("Emulator", emulatorNewMenu);
                menu3dsAddTab("Select ROM", fileMenu);
                menu3dsAddTab("Local Play", localPlayMenu);
                menu3dsSetCurrentMenuTab(1);
                menu3dsSetTabSubTitle(1, file3dsGetCurrentDir());
                selection = -1;
            }
            else
            {
                int previousEmulatorState = emulator.emulatorState;

                if (!emulatorLoadRom())
                {
                    menu3dsShowDialog("Load ROM", "Hmm... unable to load ROM.", DIALOGCOLOR_RED, optionsForOk);
                    menu3dsHideDialog();
                }
                else if (localPlayMode == LOCALPLAY_HOST)
                {
                    emulator.emulatorState = previousEmulatorState;

                    if (!impl3dsLocalPlayStartHost(
                            romFileName,
                            romFileNameFullPath))
                    {
                        menu3dsShowDialog(
                            "Local Play",
                            "Unable to create local wireless lobby.",
                            DIALOGCOLOR_RED,
                            optionsForOk
                        );
                        menu3dsHideDialog();
                        selection = -1;
                    }
                    else
                    {
                        snprintf(
                            hostLobbyGameText,
                            sizeof(hostLobbyGameText),
                            "Game: %s",
                            romFileName
                        );

                        hostLobbyActive = true;
                        hostLobbyGuestConnected = false;

                        hostStartRequested = false;
                        hostCorePrepared = false;
                        localPlayLaunchPending = false;

                        hostLobbyMenu[4].Type =
                            MENUITEM_DISABLED;
                        hostLobbyMenu[4].ID = -1;
                        hostLobbyMenu[4].Text =
                            "  Start Game";

                        snprintf(
                            hostLobbyPlayer2Text,
                            sizeof(hostLobbyPlayer2Text),
                            "Player 2: Waiting..."
                        );

                        hostLobbyMenu[3].Text =
                            hostLobbyPlayer2Text;

                        menu3dsSetFrameCallback(updateHostLobby);

                        menu3dsClearMenuTabs();
                        menu3dsAddTab("Host Lobby", hostLobbyMenu);
                        menu3dsSetCurrentMenuTab(0);

                        selection = -1;
                    }
                }
                else
                {
                    menu3dsHideMenu();
                    consoleInit(GFX_BOTTOM, NULL);
                    consoleClear();
                    return;
                }
            }
        }
        else if (selection == 6201)
        {
            if (impl3dsLocalPlayHostBeginStart())
            {
                hostStartRequested = true;
                hostCorePrepared = false;

                hostLobbyMenu[4].Type =
                    MENUITEM_DISABLED;

                hostLobbyMenu[4].ID = -1;
                hostLobbyMenu[4].Text =
                    "  Starting...";
            }

            selection = -1;
        }

        else if (
            selection >= 6300 &&
            selection < 6300 + nearbyGameCount)
        {
            int lobbyIndex = selection - 6300;

            menu3dsShowDialog(
                "Local Play",
                "Connecting...",
                DIALOGCOLOR_CYAN,
                NULL
            );

            bool joined =
                impl3dsLocalPlayJoinScannedHost(lobbyIndex);

            menu3dsHideDialog();

            if (!joined)
            {
                menu3dsShowDialog(
                    "Local Play",
                    "Unable to join this game.",
                    DIALOGCOLOR_RED,
                    optionsForOk
                );

                menu3dsHideDialog();
                selection = -1;
            }
            else
            {
                joinDiscoveryActive = false;
                joinLobbyActive = true;
                joinLobbyHostConnected = true;

                joinCorePrepared = false;
                localPlayLaunchPending = false;

                snprintf(
                    joinLobbyHostText,
                    sizeof(joinLobbyHostText),
                    "Joined: %s",
                    nearbyHostNames[lobbyIndex]
                );

                snprintf(
                    joinLobbyGameText,
                    sizeof(joinLobbyGameText),
                    "Game: %s",
                    nearbyGameNames[lobbyIndex]
                );

                snprintf(
                    joinLobbyStatusText,
                    sizeof(joinLobbyStatusText),
                    "Waiting for ROM info..."
                );

                joinLobbyMenu[1].Text = joinLobbyHostText;
                joinLobbyMenu[2].Text = joinLobbyGameText;
                joinLobbyMenu[3].Text = joinLobbyStatusText;

                menu3dsSetFrameCallback(updateJoinLobby);

                menu3dsClearMenuTabs();
                menu3dsAddTab("Join Lobby", joinLobbyMenu);
                menu3dsSetCurrentMenuTab(0);

                selection = -1;
            }
        }

        else if (selection == 6101)
        {
            localPlayMode = LOCALPLAY_SINGLE;
            updateLocalPlayMenu();
        }
        else if (selection == 6102)
        {
            localPlayMode = LOCALPLAY_HOST;
            updateLocalPlayMenu();

            menu3dsSetCurrentMenuTab(1);
        }
        else if (selection == 6103)
        {
            localPlayMode = LOCALPLAY_JOIN;
            updateLocalPlayMenu();

            menu3dsShowDialog(
                "Local Play",
                "Searching for nearby games...",
                DIALOGCOLOR_CYAN,
                NULL
            );

            nearbyGameCount = impl3dsLocalPlayScanHosts(
                nearbyHostNames,
                nearbyGameNames,
                LOCALPLAY_MAX_LOBBIES
            );

            menu3dsHideDialog();

            if (nearbyGameCount <= 0)
            {
                menu3dsShowDialog(
                    "Local Play",
                    "No nearby games found.",
                    DIALOGCOLOR_RED,
                    optionsForOk
                );

                menu3dsHideDialog();
            }
            else
            {
                buildNearbyGamesMenu();

                joinDiscoveryActive = true;
                menu3dsSetFrameCallback(NULL);

                menu3dsClearMenuTabs();
                menu3dsAddTab("Join", nearbyGamesMenu);
                menu3dsSetCurrentMenuTab(0);

                selection = -1;
            }
        }
        else if (selection == 6001)
        {
            int result = menu3dsShowDialog("Exit",  "Leaving so soon?", DIALOGCOLOR_RED, optionsForNoYes);
            menu3dsHideDialog();

            if (result == 1)
            {
                emulator.emulatorState = EMUSTATE_END;
                return;
            }
        }

        selection = -1;
    }
    while (selection == -1);

    menu3dsHideMenu();

}

bool IsFileExists(const char * filename) {
    if (FILE * file = fopen(filename, "r")) {
        fclose(file);
        return true;
    }
    return false;
}
bool menuSelectedChanged(int ID, int value)
{
    if (ID >= 50000 && ID <= 51000)
    {
        int enabled = value;
        impl3dsSetCheatEnabledFlag(ID - 50000, enabled == 1);
        cheat3dsSetCheatEnabledFlag(ID - 50000, enabled == 1);
        return false;
    }

    return impl3dsOnMenuSelectedChanged(ID, value);
}
void menuPause()
{
    gfxSetDoubleBuffering(GFX_BOTTOM, true);
    
    bool settingsUpdated = false;
    bool cheatsUpdated = false;
    bool settingsSaved = false;
    bool returnToEmulation = false;


    menu3dsClearMenuTabs();
    menu3dsAddTab("Emulator", emulatorMenu);
    menu3dsAddTab("Options", optionMenu);
    menu3dsAddTab("Controls", controlsMenu);
    menu3dsAddTab("Cheats", cheatMenu);
    menu3dsAddTab("Select ROM", fileMenu);

    impl3dsCopyMenuToOrFromSettings(false);

    int previousFileID = fileFindLastSelectedFile();
    menu3dsSetTabSubTitle(0, NULL);
    menu3dsSetTabSubTitle(1, NULL);
    menu3dsSetTabSubTitle(2, NULL);
    menu3dsSetTabSubTitle(3, NULL);
    menu3dsSetTabSubTitle(4, file3dsGetCurrentDir());
    if (previousFileID >= 0)
        menu3dsSetSelectedItemIndexByID(4, previousFileID);
    menu3dsSetCurrentMenuTab(0);
    menu3dsSetTransferGameScreen(true);

    bool animateMenu = true;

    while (true)
    {
        if (appExiting)
        {
            break;
        }

        int selection = menu3dsShowMenu(menuSelectedChanged, animateMenu);
        animateMenu = false;

        if (selection == -1 || selection == 1000)
        {
            returnToEmulation = true;

            break;
        }
        else if (selection < 1000)
        {
            romFileName = fileList[selection].c_str();
            if (romFileName[0] == 1)
            {
                if (strcmp(romFileName, "\x01 ..") == 0)
                    file3dsGoToParentDirectory();
                else
                    file3dsGoToChildDirectory(&romFileName[2]);

                fileGetAllFiles();
                menu3dsClearMenuTabs();
                menu3dsAddTab("Emulator", emulatorMenu);
                menu3dsAddTab("Options", optionMenu);
                menu3dsAddTab("Controls", controlsMenu);
                menu3dsAddTab("Cheats", cheatMenu);
                menu3dsAddTab("Select ROM", fileMenu);
                menu3dsSetCurrentMenuTab(4);
                menu3dsSetTabSubTitle(4, file3dsGetCurrentDir());
            }
            else
            {
                strncpy(romFileNameLastSelected, romFileName, _MAX_PATH);

                bool loadRom = true;
                if (settings3DS.AutoSavestate) {
                    menu3dsShowDialog("Save State", "Autosaving state...", DIALOGCOLOR_RED, NULL);
                    bool result = impl3dsSaveState(0);
                    menu3dsHideDialog();

                    if (!result) {
                        int choice = menu3dsShowDialog("Autosave failure", "Automatic savestate writing failed.\nLoad chosen game anyway?", DIALOGCOLOR_RED, optionsForNoYes);
                        if (choice != 1) {
                            loadRom = false;
                        }
                    }
                }

                if (loadRom)
                {
                    if (impl3dsCopyMenuToOrFromSettings(true))
                    {
                        emulatorSettingsSave(true, true, false);
                    }
                    else
                    {
                        emulatorSettingsSave(true, false, false);
                    }
                    settingsSaved = true;

                    if (!emulatorLoadRom())
                    {
                        menu3dsShowDialog("Load ROM", "Hmm... unable to load ROM.", DIALOGCOLOR_RED, optionsForOk);
                        menu3dsHideDialog();
                    }
                    else
                        break;
                }
            }
        }
        else if (selection >= 2001 && selection <= 2010)
        {
            int slot = selection - 2000;
            char text[200];
           
            sprintf(text, "Saving into slot %d...\nThis may take a while", slot);
            menu3dsShowDialog("Savestates", text, DIALOGCOLOR_CYAN, NULL);
            bool result = impl3dsSaveState(slot);
            menu3dsHideDialog();

            if (result)
            {
                sprintf(text, "Slot %d save completed.", slot);
                result = menu3dsShowDialog("Savestates", text, DIALOGCOLOR_GREEN, optionsForOk);
                menu3dsHideDialog();
            }
            else
            {
                sprintf(text, "Oops. Unable to save slot %d!", slot);
                result = menu3dsShowDialog("Savestates", text, DIALOGCOLOR_RED, optionsForOk);
                menu3dsHideDialog();
            }

            menu3dsSetSelectedItemIndexByID(0, 1000);
        }
        else if (selection >= 3001 && selection <= 3010)
        {
            int slot = selection - 3000;
            char text[200];

            bool result = impl3dsLoadState(slot);
            if (result)
            {
                emulator.emulatorState = EMUSTATE_EMULATE;
                consoleClear();
                break;
            }
            else
            {
                sprintf(text, "Oops. Unable to load slot %d!", slot);
                menu3dsShowDialog("Savestates", text, DIALOGCOLOR_RED, optionsForOk);
                menu3dsHideDialog();
            }
        }
        else if (selection == 4001)
        {
            menu3dsShowDialog("Screenshot", "Now taking a screenshot...\nThis may take a while.", DIALOGCOLOR_CYAN, NULL);

            char ext[256];
            const char *path = NULL;

            int i = 1;
            while (i <= 999)
            {
                snprintf(ext, 255, ".b%03d.bmp", i);
                path = file3dsReplaceFilenameExtension(romFileNameFullPath, ext);
                if (!IsFileExists(path))
                    break;
                path = NULL;
                i++;
            }

            bool success = false;
            if (path)
            {
                success = menu3dsTakeScreenshot(path);
            }
            menu3dsHideDialog();

            if (success)
            {
                char text[600];
                snprintf(text, 600, "Done! File saved to %s", path);
                menu3dsShowDialog("Screenshot", text, DIALOGCOLOR_GREEN, optionsForOk);
                menu3dsHideDialog();
            }
            else 
            {
                menu3dsShowDialog("Screenshot", "Oops. Unable to take screenshot!", DIALOGCOLOR_RED, optionsForOk);
                menu3dsHideDialog();
            }
        }
        else if (selection == 5001)
        {
            int result = menu3dsShowDialog("Reset Console", "Are you sure?", DIALOGCOLOR_RED, optionsForNoYes);
            menu3dsHideDialog();

            if (result == 1)
            {
                impl3dsResetConsole();
                emulator.emulatorState = EMUSTATE_EMULATE;
                consoleClear();

                break;
            }
            
        }
        else if (selection == 6001)
        {
            int result = menu3dsShowDialog("Exit",  "Leaving so soon?", DIALOGCOLOR_RED, optionsForNoYes);
            if (result == 1)
            {
                emulator.emulatorState = EMUSTATE_END;

                break;
            }
            else
                menu3dsHideDialog();
            
        }
        else
        {
            bool endMenu = impl3dsOnMenuSelected(selection);
            if (endMenu)
            {
                returnToEmulation = true;
                break;
            }
        }

    }

    menu3dsHideMenu();

    if (!settingsSaved && impl3dsCopyMenuToOrFromSettings(true))
    {
        emulatorSettingsSave(true, true, true);
    }
    impl3dsApplyAllSettings();

    cheat3dsSaveCheatTextFile (file3dsReplaceFilenameExtension(romFileNameFullPath, ".chx"));

    if (returnToEmulation)
    {
        emulator.emulatorState = EMUSTATE_EMULATE;
        consoleClear();
    }

}

SMenuItem cheatMenu[401] =
{
    MENU_MAKE_HEADER2   ("Cheats"),
    MENU_MAKE_LASTITEM  ()
};


char *noCheatsText[] {
    "",
    "    No cheats available for this game ",
    "",
    "    To enable cheats:  ",
    "      Copy your file into the same folder as  ",
    "      ROM file and make sure it has the same name. ",
    "",
    "      If your ROM filename is: ",
    "          MyGame.abc",
    "      Then your cheat filename must be: ",
    "          MyGame.CHX",
    "",
    "    Refer to readme.md for the .CHX file format. ",
    ""
     };
void emulatorInitialize()
{
    emulator.enableDebug = false;
    emulator.emulatorState = 0;
    emulator.waitBehavior = 0;

    file3dsInitialize();

    romFileNameLastSelected[0] = 0;

    if (!gpu3dsInitialize())
    {
        printf ("Unable to initialize GPU\n");
        exit(0);
    }

    printf ("Initializing...\n");

    if (!impl3dsInitializeCore())
    {
        printf ("Unable to initialize emulator core\n");
        exit(0);
    }

    if (!snd3dsInitialize())
    {
        printf ("Unable to initialize CSND\n");
        exit (0);
    }

    ui3dsInitialize();

    /*if (romfsInit()!=0)
    {
        printf ("Unable to initialize romfs\n");
        exit (0);
    }
    */
    printf ("Initialization complete\n");

    osSetSpeedupEnable(1);

    enableExitHook();

    emulatorSettingsLoad(true, false, true);

    if (file3dsGetCurrentDir()[0] == 0)
        file3dsInitialize();
}

void emulatorFinalize()
{
    consoleClear();

    impl3dsFinalize();

#ifndef EMU_RELEASE
    printf("gspWaitForP3D:\n");
#endif
    gspWaitForVBlank();
    gpu3dsWaitForPreviousFlush();
    gspWaitForVBlank();

#ifndef EMU_RELEASE
    printf("snd3dsFinalize:\n");
#endif
    snd3dsFinalize();

#ifndef EMU_RELEASE
    printf("gpu3dsFinalize:\n");
#endif
    gpu3dsFinalize();

#ifndef EMU_RELEASE
    printf("ptmSysmExit:\n");
#endif
    ptmSysmExit ();

#ifndef EMU_RELEASE
    printf("hidExit:\n");
#endif
	hidExit();
    
#ifndef EMU_RELEASE
    printf("aptExit:\n");
#endif
	aptExit();
    
#ifndef EMU_RELEASE
    printf("srvExit:\n");
#endif
	srvExit();
}



bool firstFrame = true;
char frameCountBuffer[70];
void updateFrameCount()
{
    if (frameCountTick == 0)
        frameCountTick = svcGetSystemTick();

    if (frameCount60 == 0)
    {
        u64 newTick = svcGetSystemTick();
        float timeDelta = ((float)(newTick - frameCountTick))/TICKS_PER_SEC;
        int fpsmul10 = (int)((float)600 / timeDelta);

#if !defined(EMU_RELEASE) && !defined(DEBUG_CPU) && !defined(DEBUG_APU)
        consoleClear();
#endif

        if (settings3DS.HideUnnecessaryBottomScrText == 0)
        {
            if (framesSkippedCount)
                snprintf (frameCountBuffer, 69, "FPS: %2d.%1d (%d skipped)\n", fpsmul10 / 10, fpsmul10 % 10, framesSkippedCount);
            else
                snprintf (frameCountBuffer, 69, "FPS: %2d.%1d \n", fpsmul10 / 10, fpsmul10 % 10);

            ui3dsDrawRect(2, 2, 200, 16, 0x000000);
            ui3dsDrawStringWithNoWrapping(2, 2, 200, 16, 0x7f7f7f, HALIGN_LEFT, frameCountBuffer);
        }

        frameCount60 = 60;
        framesSkippedCount = 0;


#if !defined(EMU_RELEASE) && !defined(DEBUG_CPU) && !defined(DEBUG_APU)
        printf ("\n\n");
        for (int i=0; i<100; i++)
        {
            t3dsShowTotalTiming(i);
        }
        t3dsResetTimings();
#endif
        frameCountTick = newTick;

    }

    frameCount60--;
}

void emulatorLoop()
{
    emulator.waitBehavior = WAIT_FULL;

    int emuFramesSkipped = 0;
    long emuFrameTotalActualTicks = 0;
    long emuFrameTotalAccurateTicks = 0;

    bool firstFrame = true;

    gpu3dsResetState();

    frameCount60 = 60;
    frameCountTick = 0;
    framesSkippedCount = 0;

    long startFrameTick = svcGetSystemTick();

    bool skipDrawingFrame = false;

    consoleInit(GFX_BOTTOM, NULL);
    gfxSetDoubleBuffering(GFX_BOTTOM, false);
    menu3dsDrawBlackScreen();
    if (settings3DS.HideUnnecessaryBottomScrText == 0)
    {
        ui3dsDrawStringWithNoWrapping(0, 100, 320, 115, 0x7f7f7f, HALIGN_CENTER, "Touch screen for menu");
    }


    snd3dsStartPlaying();


    impl3dsEmulationBegin();


	while (true)
	{


        startFrameTick = svcGetSystemTick();
        aptMainLoop();

        if (appExiting)
            break;

        gpu3dsStartNewFrame();
        

        gpu3dsCheckSlider();
        updateFrameCount();


    	input3dsScanInputForEmulation();
        if (emulator.emulatorState != EMUSTATE_EMULATE)
            break;

        impl3dsEmulationRunOneFrame(firstFrame, skipDrawingFrame);

        firstFrame = false; 

#ifndef EMU_RELEASE
        if (emulator.isReal3DS)
#endif
        {
            int keysHeld = input3dsGetCurrentKeysHeld();
            emulator.fastForwarding = false;
            if ((settings3DS.UseGlobalEmuControlKeys && (settings3DS.GlobalButtonHotkeyDisableFramelimit & keysHeld)) ||
                (!settings3DS.UseGlobalEmuControlKeys && (settings3DS.ButtonHotkeyDisableFramelimit & keysHeld))) 
                emulator.fastForwarding = true;

            long currentTick = svcGetSystemTick();
            long actualTicksThisFrame = currentTick - startFrameTick;
            long ticksPerFrame = settings3DS.TicksPerFrame;
            if (emulator.fastForwarding)
                ticksPerFrame = TICKS_PER_FRAME_FASTFORWARD;

            emuFrameTotalActualTicks += actualTicksThisFrame;
            emuFrameTotalAccurateTicks += ticksPerFrame;

            int isSlow = 0;

            long skew = emuFrameTotalAccurateTicks - emuFrameTotalActualTicks;

            if (skew < 0)
            {
                if (skew < -ticksPerFrame/10 && emuFramesSkipped < settings3DS.MaxFrameSkips)
                {
                    skipDrawingFrame = true;
                    emuFramesSkipped++;

                    framesSkippedCount++;
                }
                else
                {
                    skipDrawingFrame = false;

                    if (emuFramesSkipped >= settings3DS.MaxFrameSkips)
                    {
                        emuFramesSkipped = 0;
                        emuFrameTotalActualTicks = actualTicksThisFrame;
                        emuFrameTotalAccurateTicks = ticksPerFrame;
                    }
                }
            }
            else
            {

                float timeDiffInMilliseconds = (float)skew * 1000000 / TICKS_PER_SEC;
                if (emulator.waitBehavior == WAIT_HALF)
                    timeDiffInMilliseconds /= 2;
                else if (emulator.waitBehavior == EMU_WAIT_NONE)
                    timeDiffInMilliseconds = 1;
                emulator.waitBehavior = WAIT_FULL;

                emuFrameTotalActualTicks = 0;
                emuFrameTotalAccurateTicks = 0;
                emuFramesSkipped = 0;

                svcSleepThread ((long)(timeDiffInMilliseconds * 1000));
                skipDrawingFrame = false;
            }

        }

	}

    snd3dsStopPlaying();

    svcSleepThread(500000);
}

int main()
{
    emulatorInitialize();
    clearTopScreenWithLogo();

    menuSelectFile();

    while (true)
    {
        if (appExiting)
            goto quit;

        switch (emulator.emulatorState)
        {
            case EMUSTATE_PAUSEMENU:
                menuPause();
                break;

            case EMUSTATE_EMULATE:
                emulatorLoop();
                break;

            case EMUSTATE_END:
                goto quit;

        }

    }

quit:
    if (emulator.emulatorState > 0 && settings3DS.AutoSavestate)
        impl3dsLoadState(0);

    printf("emulatorFinalize:\n");
    emulatorFinalize();
    printf ("Exiting...\n");
	exit(0);
}
