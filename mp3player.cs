#nullable disable
using FMOD;
using FMOD.Studio;
using HarmonyLib;
using mp3player;
using RedLoader;
using RedLoader.Utils;
using Sons.Items;
using SonsSdk;
using SUI;
using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Reflection;
using System.Runtime.InteropServices;
using TheForest.Utils;
using UnityEngine;
using static mp3player.CustomRadioMod;
using Array = System.Array;
using Exception = System.Exception;
using IntPtr = System.IntPtr;
using Math = System.Math;
using StringComparer = System.StringComparer;
using TimeSpan = System.TimeSpan;

namespace mp3player
{
    public class CustomRadioMod : SonsMod
    {
        public static readonly List<string> Mp3Files = new List<string>();
        private static readonly List<string> _playlistNames = new List<string>();
        private static readonly Dictionary<string, List<string>> _playlistTracks = new Dictionary<string, List<string>>(StringComparer.OrdinalIgnoreCase);
        private static int _currentPlaylistIndex = 0;
        private static int _currentTrackIndex = 0;
        private static int _lastPlayedTrackIndex = 0;
        private static bool _isRepeatSingleTrack = false;
        private static bool _isShuffleEnabled = false;
        private static readonly System.Random _rng = new System.Random();

        public static FMOD.Studio.System StudioSystem;
        public static FMOD.System CoreSystem;
        public static bool IsFmodReady = false;

        // Track active radios/boomboxes in the scene for hotkeys
        public static readonly List<Radio> ActiveBoomboxes = new List<Radio>();
        public static readonly List<RadioPlayer> ActiveRadioPlayers = new List<RadioPlayer>();
        public static bool ForceSkipRequested = false;
        public static bool IsCartStartingUp = false;
        public static bool IsNaturalAutoAdvance = false;
        public static bool KeepCurrentTrackOnRestart = false;
        public static bool SuppressNextHudPopup = false;
        public static bool IsInsideRadioUpdate = false;

        // Audible and LCD culling range (60 meters = 3600f squared)
        public const float MaxAudibleDistanceSq = 3600f;

        // Cached Main Camera reference to eliminate repeated Unity tag lookups every frame
        private static Camera _cachedMainCamera;
        private static Camera GetMainCamera()
        {
            if (_cachedMainCamera == null)
            {
                _cachedMainCamera = Camera.main;
            }
            return _cachedMainCamera;
        }

        // Per-instance state keyed by Unity InstanceID (strongly-typed Dictionary<int, ...>, zero boxing)
        public class RadioRuntimeState
        {
            public bool IsRegistered;
            public bool WasOn;
            public bool CachedInRange;
            public bool NeedsModeRestart;
            public bool IsUserPaused;
            public float FirstSeenTime;
            public float LastRangeCheckTime;
            public float LastSyncTime;
            public float LastFinishCheckTime;
            public float LastRestartTime;
            public float LastStartRequestTime;
            public float LastChannelLookupTime;
            public EventInstance LastPlayingEvent;
            public BoomboxWorldLcdState LcdState;
        }

        private static readonly Dictionary<int, RadioRuntimeState> _radioStates = new Dictionary<int, RadioRuntimeState>();

        public static RadioRuntimeState GetOrCreateState(int instanceId)
        {
            RadioRuntimeState state;
            if (!_radioStates.TryGetValue(instanceId, out state))
            {
                state = new RadioRuntimeState();
                _radioStates[instanceId] = state;
            }
            return state;
        }

        public static bool TryGetState(int instanceId, out RadioRuntimeState state)
        {
            return _radioStates.TryGetValue(instanceId, out state);
        }

        // Strongly-typed, thread-safe tables for active raw FMOD Core Channel pointers and sound handles
        private static readonly ConcurrentDictionary<IntPtr, IntPtr> _instanceToChannelMap = new ConcurrentDictionary<IntPtr, IntPtr>();
        private static readonly ConcurrentDictionary<IntPtr, IntPtr> _instanceToDspMap = new ConcurrentDictionary<IntPtr, IntPtr>();
        private static readonly ConcurrentDictionary<IntPtr, IntPtr> _instanceToSoundMap = new ConcurrentDictionary<IntPtr, IntPtr>();
        private static readonly ConcurrentDictionary<IntPtr, IntPtr> _activePlayingSounds = new ConcurrentDictionary<IntPtr, IntPtr>();
        private static readonly ConcurrentDictionary<IntPtr, float> _instanceStartTimes = new ConcurrentDictionary<IntPtr, float>();
        private static readonly ConcurrentDictionary<IntPtr, PlaybackTimerState> _instanceTimerStates = new ConcurrentDictionary<IntPtr, PlaybackTimerState>();
        private static readonly Dictionary<string, uint> _trackLengthMsCache = new Dictionary<string, uint>(StringComparer.OrdinalIgnoreCase);

        private static readonly object _fmodNativeLock = new object();
        private static float _currentFadeMultiplier = 1.0f;
        private static volatile bool _isEscapeMenuOpen = false;
        private static volatile bool _isWindowForeground = true;
        private static float _lastWindowFocusCheckTime = -1f;
        private static readonly Stopwatch _fadeStopwatch = Stopwatch.StartNew();
        private static double _lastFadeTickSec = 0.0;
        private static System.Threading.Timer _fadeTimer;
        private const float FadeDurationSeconds = 1.0f;

        public class PlaybackTimerState
        {
            public uint TotalLengthMs;
            public uint AnchorPositionMs;
            public float AnchorRealtime;
            public bool ChannelAnchored;
            public uint PendingStartSeekMs;
        }

        // 3D Cube + Unlit Material LCD per boombox using pinned Color32[] + LoadRawTextureData (works on stripped IL2CPP)
        public class BoomboxWorldLcdState
        {
            public GameObject RootObj;
            public Texture2D LcdTex;
            public Color32[] PixelBuffer;
            public GCHandle BufferPinHandle;
            public bool IsBufferPinned;
            public string LastDisplayedText = "";
            public float NextPollTime = 0f;
            public bool Failed = false;

            public void UploadBufferToTexture()
            {
                if (LcdTex == null || !IsBufferPinned) return;
                int byteSize = LcdTexWidth * LcdTexHeight * 4;
                LcdTex.LoadRawTextureData(BufferPinHandle.AddrOfPinnedObject(), byteSize);
                LcdTex.Apply(false);

            }

            public void CleanupAssets()
            {
                if (IsBufferPinned)
                {
                    BufferPinHandle.Free();
                    IsBufferPinned = false;
                }
                if (RootObj != null)
                {
                    UnityEngine.Object.Destroy(RootObj);
                    RootObj = null;
                }
                if (LcdTex != null)
                {
                    UnityEngine.Object.Destroy(LcdTex);
                    LcdTex = null;
                }
                PixelBuffer = null;
            }
        }
        // Pre-rendered 4-ring supersampled anti-aliased glyph stamps using Color32
        private static readonly Dictionary<char, Color32[]> _glyphStampCache = new Dictionary<char, Color32[]>();
        private const int LcdTexWidth = 520;
        private const int LcdTexHeight = 198;
        private const int GlyphScale = 12;
        private const int GlyphSpacing = 10;
        private const int StampPad = 6;
        private static readonly Color32 LcdBgColor32 = new Color32(13, 15, 20, 255);
        private static readonly Color32 LcdFgColor32 = new Color32(92, 237, 255, 255);
        private static readonly float[] Bayer4x4 = new float[]
        {
             0f / 16f,  8f / 16f,  2f / 16f, 10f / 16f,
            12f / 16f,  4f / 16f, 14f / 16f,  6f / 16f,
             3f / 16f, 11f / 16f,  1f / 16f,  9f / 16f,
            15f / 16f,  7f / 16f, 13f / 16f,  5f / 16f
        };

        // Locked-in aligned boombox LCD coordinates and scale
        private static float _livePosX = 0.0000f;
        private static float _livePosY = 0.0970f;
        private static float _livePosZ = 0.0820f;
        private static float _liveRotY = 0.0f;
        private static float _liveScaleX = 0.00090f;
        private static float _liveScaleY = 0.00024f;


        // Track when the player actively enters the game world
        private static float _worldReadyTime = -1f;

        // Custom UnityEngine.UI HUD Box
        private static GameObject _hudCanvasObj;
        private static GameObject _hudBoxObj;
        private static UnityEngine.UI.Text _hudPrefixLabel;
        private static UnityEngine.UI.Text _hudValueLabel;
        private static RectTransform _hudValueRect;
        private static float _hudTimer = 0f;
        private static float _hudScrollDistance = 0f;
        private static float _hudScrollElapsed = 0f;
        private static bool _hudScrollFinished = false;
        private const float HudDuration = 3.0f;
        private const float HudScrollSpeed = 55.0f;
        private const float HudScrollStartDelay = 0.65f;
        private const float HudScrollEndHold = 0.65f;
        public static ConfigCategory _configCategory = null;
        public static ConfigEntry<string> _skipKeyEntry;
        public static ConfigEntry<string> _previousKeyEntry;
        public static ConfigEntry<string> _fastForwardKeyEntry;
        public static ConfigEntry<string> _rewindKeyEntry;
        public static ConfigEntry<string> _repeatKeyEntry;
        public static ConfigEntry<string> _shuffleKeyEntry;
        public static ConfigEntry<float> _controlRadiusEntry;
        public static ConfigEntry<bool> _scanTracksEntry;
        public static ConfigEntry<bool> _boombox2DAudioEntry;
        public static ConfigEntry<string> _playPauseKeyEntry;
        public static ConfigEntry<string> _switchPlaylistKeyEntry;
        public static ConfigEntry<float> _walkman2DVolumeEntry;
        public static ConfigEntry<string> _volumeUpKeyEntry;
        public static ConfigEntry<string> _volumeDownKeyEntry;
        public static ConfigEntry<string> _volumeStepPercentEntry;
        private static EventInstance _standalone2DEvent;
        private static bool _isStandalone2DPaused = false;
        private static float _standalone2DEndTime = float.MaxValue;
        public static int _savedTrackIndex = 0;
        public static uint _savedPositionMs = 0;
        public static bool _resumeSavedPositionOnNextStart = false;
        public static bool _pending2DAutoResume = false;
        private static bool _wasPlayPauseKeyDown = false;
        private static string _cachedPlayPauseStr = "";
        private static int _cachedPlayPauseVKey = 0xBA;
        private static bool _wasSwitchPlaylistKeyDown = false;
        private static string _cachedSwitchPlaylistStr = "";
        private static int _cachedSwitchPlaylistVKey = 0xDE;
        private static bool _wasSkipKeyDown = false;
        private static bool _wasPreviousKeyDown = false;
        private static bool _wasFastForwardKeyDown = false;
        private static bool _wasRewindKeyDown = false;
        private static bool _wasRepeatKeyDown = false;
        private static bool _wasShuffleKeyDown = false;
        // Cached virtual key codes so we avoid string parsing every frame
        private static string _cachedSkipStr = "";
        private static int _cachedSkipVKey = 0xDC;
        private static string _cachedPrevStr = "";
        private static int _cachedPrevVKey = 0x50;
        private static string _cachedFfStr = "";
        private static int _cachedFfVKey = 0x27;
        private static string _cachedRwStr = "";
        private static int _cachedRwVKey = 0x25;
        private static string _cachedRepeatStr = "";
        private static int _cachedRepeatVKey = 0x4F;
        private static string _cachedShuffleStr = "";
        private static int _cachedShuffleVKey = 0x4B;
        private static string _cachedVolUpStr = "";
        private static int _cachedVolUpVKey = 0x6B;
        private static string _cachedVolDownStr = "";
        private static int _cachedVolDownVKey = 0x6D;
        private static bool _wasVolUpKeyDown = false;
        private static bool _wasVolDownKeyDown = false;
        private static float _volumeHoldTimer = 0f;
        private const float VolumeInitialHoldDelay = 0.35f;
        private const float VolumeRepeatInterval = 0.08f;
        public static float _current3DVolume = 1.0f;

        [DllImport("user32.dll")]
        private static extern short GetAsyncKeyState(int vKey);

        [DllImport("user32.dll")]
        private static extern IntPtr GetForegroundWindow();

        [DllImport("user32.dll")]
        private static extern uint GetWindowThreadProcessId(IntPtr hWnd, out uint lpdwProcessId);

        private static readonly uint _currentProcessId = (uint)Process.GetCurrentProcess().Id;

        [StructLayout(LayoutKind.Sequential)]
        public struct NativeProgrammerSoundProps
        {
            public IntPtr name;
            public IntPtr sound;
            public int subsoundIndex;
        }

        [UnmanagedFunctionPointer(CallingConvention.Cdecl)]
        private delegate RESULT NativeEventCallback(EVENT_CALLBACK_TYPE type, IntPtr eventInstance, IntPtr parameters);

        [DllImport("fmodstudio", CallingConvention = CallingConvention.Cdecl)]
        private static extern RESULT FMOD_Studio_EventInstance_SetCallback(
        IntPtr eventInstance,
        IntPtr callback,
        EVENT_CALLBACK_TYPE callbackmask
        );

        [DllImport("fmodstudio", CallingConvention = CallingConvention.Cdecl)]
        private static extern RESULT FMOD_Studio_EventInstance_GetChannelGroup(IntPtr eventInstance, out IntPtr group);
        [DllImport("fmodstudio", CallingConvention = CallingConvention.Cdecl)]
        private static extern RESULT FMOD_ChannelGroup_GetNumChannels(IntPtr channelgroup, out int numchannels);
        [DllImport("fmodstudio", CallingConvention = CallingConvention.Cdecl)]
        private static extern RESULT FMOD_ChannelGroup_GetChannel(IntPtr channelgroup, int index, out IntPtr channel);
        [DllImport("fmodstudio", CallingConvention = CallingConvention.Cdecl)]
        private static extern RESULT FMOD_ChannelGroup_GetNumGroups(IntPtr channelgroup, out int numgroups);
        [DllImport("fmodstudio", CallingConvention = CallingConvention.Cdecl)]
        private static extern RESULT FMOD_ChannelGroup_GetGroup(IntPtr channelgroup, int index, out IntPtr group);
        [DllImport("fmodstudio", CallingConvention = CallingConvention.Cdecl)]
        private static extern RESULT FMOD_Channel_IsPlaying(IntPtr channel, out int isplaying);
        [DllImport("fmodstudio", CallingConvention = CallingConvention.Cdecl)]
        private static extern RESULT FMOD_Channel_SetVolume(IntPtr channel, float volume);
        [DllImport("fmodstudio", CallingConvention = CallingConvention.Cdecl)]
        private static extern RESULT FMOD_Channel_GetPosition(IntPtr channel, out uint position, uint postype);
        [DllImport("fmodstudio", CallingConvention = CallingConvention.Cdecl)]
        private static extern RESULT FMOD_Channel_SetPosition(IntPtr channel, uint position, uint postype);

        [DllImport("fmodstudio", CallingConvention = CallingConvention.Cdecl)]
        private static extern RESULT FMOD_Sound_GetLength(IntPtr sound, out uint length, uint lengthtype);
        [DllImport("fmodstudio", CallingConvention = CallingConvention.Cdecl)]
        private static extern RESULT FMOD_System_CreateDSPByType(IntPtr system, int type, out IntPtr dsp);
        [DllImport("fmodstudio", CallingConvention = CallingConvention.Cdecl)]
        private static extern RESULT FMOD_ChannelGroup_AddDSP(IntPtr channelgroup, int index, IntPtr dsp);
        [DllImport("fmodstudio", CallingConvention = CallingConvention.Cdecl)]
        private static extern RESULT FMOD_ChannelGroup_RemoveDSP(IntPtr channelgroup, IntPtr dsp);
        [DllImport("fmodstudio", CallingConvention = CallingConvention.Cdecl)]
        private static extern RESULT FMOD_DSP_SetParameterFloat(IntPtr dsp, int index, float value);
        [DllImport("fmodstudio", CallingConvention = CallingConvention.Cdecl)]
        private static extern RESULT FMOD_DSP_Release(IntPtr dsp);
        private const uint FMOD_TIMEUNIT_MS = 0x00000001;
        private const int FMOD_DSP_TYPE_LIMITER = 27;
        private static NativeEventCallback _managedCallback = null;
        private static IntPtr _nativeCallbackPtr = IntPtr.Zero;
        private static Bank _customBank;
        private static string _modFolder = "";
        public static readonly Il2CppSystem.Guid CustomEventGuid = Il2CppSystem.Guid.Parse("b8306987-8d77-4184-8718-7367879cabbf");
        public static readonly Il2CppSystem.Guid CustomEvent2DGuid = Il2CppSystem.Guid.Parse("{e2379ac8-c6c2-4cdc-8e23-75891c71d08e}");
        public static void RegisterBoombox(Radio radio, RadioRuntimeState state = null)
        {
            if (radio == null) return;
            if (state == null) state = GetOrCreateState(radio.GetInstanceID());
            if (!state.IsRegistered)
            {
                state.IsRegistered = true;
                state.FirstSeenTime = Time.realtimeSinceStartup;
                ActiveBoomboxes.Add(radio);
            }
        }
        public static void RegisterRadioPlayer(RadioPlayer rp, RadioRuntimeState state = null)
        {
            if (rp == null) return;
            if (state == null) state = GetOrCreateState(rp.GetInstanceID());
            if (!state.IsRegistered)
            {
                state.IsRegistered = true;
                ActiveRadioPlayers.Add(rp);
            }
        }
        private static bool IsSupportedAudioFile(string path)
        {
            string ext = Path.GetExtension(path);
            return ext.Equals(".mp3", StringComparison.OrdinalIgnoreCase)
                || ext.Equals(".wav", StringComparison.OrdinalIgnoreCase)
                || ext.Equals(".ogg", StringComparison.OrdinalIgnoreCase)
                || ext.Equals(".flac", StringComparison.OrdinalIgnoreCase);
        }

        private static List<string> CollectAudioFilesInDirectory(string dirPath)
        {
            var list = new List<string>();
            if (!Directory.Exists(dirPath)) return list;
            string[] files = Directory.GetFiles(dirPath);
            Array.Sort(files, StringComparer.OrdinalIgnoreCase);
            for (int i = 0; i < files.Length; i++)
            {
                if (IsSupportedAudioFile(files[i]))
                {
                    list.Add(files[i]);
                }
            }
            return list;
        }

        private static void ApplyActivePlaylistSelection(string desiredName)
        {
            if (_playlistNames.Count == 0)
            {
                Mp3Files.Clear();
                _currentPlaylistIndex = 0;
                _currentTrackIndex = 0;
                _lastPlayedTrackIndex = 0;
                return;
            }
            int foundIdx = 0;
            if (!string.IsNullOrWhiteSpace(desiredName))
            {
                for (int i = 0; i < _playlistNames.Count; i++)
                {
                    if (_playlistNames[i].Equals(desiredName.Trim(), StringComparison.OrdinalIgnoreCase))
                    {
                        foundIdx = i;
                        break;
                    }
                }
            }
            _currentPlaylistIndex = foundIdx;
            string selectedName = _playlistNames[_currentPlaylistIndex];
            Mp3Files.Clear();
            List<string> tracks;
            if (_playlistTracks.TryGetValue(selectedName, out tracks) && tracks != null)
            {
                Mp3Files.AddRange(tracks);
            }
            _currentTrackIndex = 0;
            _lastPlayedTrackIndex = 0;
        }
            public static void RescanTracksFolder()
        {
            if (string.IsNullOrEmpty(_modFolder)) return;
            string tracksFolder = Path.Combine(_modFolder, "Tracks");
            Directory.CreateDirectory(tracksFolder);

            _playlistNames.Clear();
            _playlistTracks.Clear();
            _trackLengthMsCache.Clear();

            var allTracks = new List<string>();
            var rootTracks = CollectAudioFilesInDirectory(tracksFolder);
            allTracks.AddRange(rootTracks);

            string[] subDirs = Directory.GetDirectories(tracksFolder);
            Array.Sort(subDirs, StringComparer.OrdinalIgnoreCase);
            var folderNamesWithTracks = new List<string>();

            for (int i = 0; i < subDirs.Length; i++)
            {
                string folderTracksDir = subDirs[i];
                var folderTracks = CollectAudioFilesInDirectory(folderTracksDir);
                if (folderTracks.Count > 0)
                {
                    string folderName = Path.GetFileName(folderTracksDir);
                    if (!_playlistTracks.ContainsKey(folderName))
                    {
                        _playlistTracks[folderName] = folderTracks;
                        folderNamesWithTracks.Add(folderName);
                        allTracks.AddRange(folderTracks);
                    }
                }
            }

            _playlistNames.Add("All Playlists");
            _playlistTracks["All Playlists"] = allTracks;

            if (rootTracks.Count > 0 && folderNamesWithTracks.Count > 0)
            {
                _playlistNames.Add("Root");
                _playlistTracks["Root"] = rootTracks;
            }

            for (int i = 0; i < folderNamesWithTracks.Count; i++)
            {
                _playlistNames.Add(folderNamesWithTracks[i]);
            }

            ApplyActivePlaylistSelection("All Playlists");
        }
        protected override void OnInitializeMod()
        {
            string baseModsDir = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
            _modFolder = baseModsDir.EndsWith("mp3player", StringComparison.OrdinalIgnoreCase)
            ? baseModsDir
            : Path.Combine(baseModsDir, "mp3player");
            RescanTracksFolder();
            RLog.Msg($"mp3player: Loaded {Mp3Files.Count} custom MP3 tracks.");
            BuildGlyphStampCache();
            _managedCallback = ProgrammerSoundCallback;
            _nativeCallbackPtr = Marshal.GetFunctionPointerForDelegate(_managedCallback);
            _lastFadeTickSec = _fadeStopwatch.Elapsed.TotalSeconds;
            _fadeTimer = new System.Threading.Timer(OnFadeTimerTick, null, 25, 25);
            GlobalEvents.OnUpdate.Subscribe(HandleUpdate);
            HarmonyInstance.PatchAll();
        }
        protected override void OnDeinitializeMod()
        {
            try
            {
                _configCategory?.SaveToFile(false);
                SyncVolumeModRadius(false);
                _fadeTimer?.Dispose();
                _fadeTimer = null;
                _instanceToChannelMap.Clear();
            }
            catch { }
        }
        private static bool QueryWindowForeground()
        {
            IntPtr fg = GetForegroundWindow();
            if (fg == IntPtr.Zero) return false;
            uint fgPid;
            GetWindowThreadProcessId(fg, out fgPid);
            return fgPid == _currentProcessId;
        }
        private static void OnFadeTimerTick(object state)
        {
            double nowSec = _fadeStopwatch.Elapsed.TotalSeconds;
            float dt = (float)(nowSec - _lastFadeTickSec);
            _lastFadeTickSec = nowSec;
            if (dt <= 0f) return;
            if (dt > 0.25f) dt = 0.25f;
            bool isForeground = _isWindowForeground;
            if (!isForeground)
            {
                isForeground = QueryWindowForeground();
                _isWindowForeground = isForeground;
            }
            bool shouldFadeOut = !isForeground || _isEscapeMenuOpen;
            float target = shouldFadeOut ? 0.0f : 1.0f;
            if (Math.Abs(_currentFadeMultiplier - target) < 0.0005f)
            {
                return;
            }
            float step = dt / FadeDurationSeconds;
            if (_currentFadeMultiplier < target)
            {
                _currentFadeMultiplier = Math.Min(target, _currentFadeMultiplier + step);
            }
            else
            {
                _currentFadeMultiplier = Math.Max(target, _currentFadeMultiplier - step);
            }
            if (_instanceToChannelMap.IsEmpty) return;
            lock (_fmodNativeLock)
            {
                foreach (var kvp in _instanceToChannelMap)
                {
                    IntPtr channelPtr = kvp.Value;
                    if (channelPtr != IntPtr.Zero)
                    {
                        int isPlaying;
                        FMOD_Channel_IsPlaying(channelPtr, out isPlaying);
                        if (isPlaying != 0)
                        {
                            float volScale = (_standalone2DEvent.isValid() && kvp.Key == _standalone2DEvent.handle)
                                ? GetWalkman2DVolume()
                                : Mathf.Clamp(_current3DVolume, 0.0f, 1.5f);
                            FMOD_Channel_SetVolume(channelPtr, _currentFadeMultiplier * volScale * 0.60f);
                        }
                    }
                }
            }
        }
        public static float GetWalkman2DVolume()
        {
            object val = ReadEntryValue(_walkman2DVolumeEntry);
            if (val is float)
            {
                return Mathf.Clamp((float)val, 0.0f, 1.5f);
            }
            return 1.0f;
        }
        private static float GetVolumeStepAmount()
        {
            string raw = ReadEntryValue(_volumeStepPercentEntry) as string;
            float percent;
            if (!string.IsNullOrWhiteSpace(raw) &&
                float.TryParse(raw.Trim().TrimEnd('%'), out percent) &&
                percent > 0f)
            {
                return Mathf.Clamp(percent / 100f, 0.01f, 1.5f);
            }
            return 0.25f;
        }
        private static void AdjustIntegratedVolume(float delta)
        {
            if (IsBoombox2DEnabled())
            {
                float cur = GetWalkman2DVolume();
                float next = Mathf.Clamp(cur + delta, 0.0f, 1.5f);
                if (_walkman2DVolumeEntry != null)
                {
                    _walkman2DVolumeEntry.Value = next;
                }
                int percent = Mathf.RoundToInt(next * 100f);
                ShowHudMessage("Headphones Volume", $"{percent}%");
                return;
            }

            _current3DVolume = Mathf.Clamp(_current3DVolume + delta, 0.0f, 1.5f);
            lock (_fmodNativeLock)
            {
                foreach (var kvp in _instanceToChannelMap)
                {
                    if (_standalone2DEvent.isValid() && kvp.Key == _standalone2DEvent.handle) continue;
                    IntPtr chPtr = kvp.Value;
                    if (chPtr != IntPtr.Zero)
                    {
                        int isPlaying;
                        FMOD_Channel_IsPlaying(chPtr, out isPlaying);
                        if (isPlaying != 0)
                        {
                            FMOD_Channel_SetVolume(chPtr, _currentFadeMultiplier * _current3DVolume * 0.60f);
                        }
                    }
                }
            }
            int radioPercent = Mathf.RoundToInt(_current3DVolume * 100f);
            ShowHudMessage("Radio Volume", $"{radioPercent}%");
        }
        public static void ClearPlaybackBookmark()
        {
            _savedPositionMs = 0;
            _resumeSavedPositionOnNextStart = false;
        }
        public static void SavePlaybackBookmark(EventInstance eventInstance, string sourceReason, bool isPaused = false, float overrideNow = -1f)
        {
            if (!eventInstance.isValid() || Mp3Files.Count == 0) return;
            PlaybackTimerState timerState;
            if (!_instanceTimerStates.TryGetValue(eventInstance.handle, out timerState) || !timerState.ChannelAnchored)
            {
                return;
            }
            float now = overrideNow >= 0f ? overrideNow : Time.realtimeSinceStartup;
            uint posMs = timerState.AnchorPositionMs;
            if (!isPaused)
            {
                float elapsedSec = Math.Max(0f, now - timerState.AnchorRealtime);
                posMs += (uint)(elapsedSec * 1000f);
            }
            if (timerState.TotalLengthMs > 1000 && posMs >= timerState.TotalLengthMs - 500)
            {
                return;
            }
            _savedTrackIndex = _lastPlayedTrackIndex % Mp3Files.Count;
            _savedPositionMs = posMs;
            _resumeSavedPositionOnNextStart = true;
        }
        public static void StopStandalone2DEvent()
        {
            _isStandalone2DPaused = false;
            _standalone2DEndTime = float.MaxValue;
            if (_standalone2DEvent.isValid())
            {
                IntPtr oldHandle = _standalone2DEvent.handle;
                _standalone2DEvent.stop(FMOD.Studio.STOP_MODE.IMMEDIATE);
                _standalone2DEvent.release();
                _standalone2DEvent = default(EventInstance);
                ReleaseSoundForInstance(oldHandle);
            }
        }
        protected override void OnSdkInitialized()
        {
            string customConfigPath = Path.Combine(LoaderEnvironment.UserDataDirectory, "mp3player.cfg");

            _configCategory = ConfigSystem.CreateCategory("mp3player", "MP3 Radio Player");
            _configCategory.SetFilePath(customConfigPath, false, false);

            _skipKeyEntry = _configCategory.CreateEntry(
                "SkipTrackKey",
                "Backslash",
                "Skip Track Key",
                "Key name to skip to next track (e.g. Backslash, N, M, PageDown, F5)."
            );
            _previousKeyEntry = _configCategory.CreateEntry(
                "PreviousTrackKey",
                "P",
                "Previous Track Key",
                "Key name to go back to the previous track (e.g. P, B, PageUp, F4)."
            );
            _fastForwardKeyEntry = _configCategory.CreateEntry(
                "FastForward30sKey",
                "RightArrow",
                "Fast Forward 30s Key",
                "Key name to jump forward 30 seconds in the current track (e.g. RightArrow, PageUp, F6)."
            );
            _rewindKeyEntry = _configCategory.CreateEntry(
                "Rewind15sKey",
                "LeftArrow",
                "Rewind 15s Key",
                "Key name to jump back 15 seconds in the current track (e.g. LeftArrow, PageDown, F7)."
            );
            _repeatKeyEntry = _configCategory.CreateEntry(
                "RepeatTrackKey",
                "O",
                "Repeat Single Track Key",
                "Key name to toggle repeating the current track on or off (e.g. O, K, J, Semicolon, F8)."
            );
            _shuffleKeyEntry = _configCategory.CreateEntry(
                "ShuffleTrackKey",
                "K",
                "Shuffle Tracks Key",
                "Key name to toggle shuffle playback mode on or off (e.g. K, J, U, F9)."
            );
            _controlRadiusEntry = _configCategory.CreateEntry(
                "ControlRadiusMeters",
                10.0f,
                "Control Radius (Meters)",
                "Maximum distance in meters from an active boombox or radio for playback hotkeys to work."
            );
            _scanTracksEntry = _configCategory.CreateEntry(
                "ScanTracksFolder",
             false,
                "Scan Tracks Folder",
                "Toggle ON or OFF to immediately rescan the Tracks folder for added or removed MP3 files.",
             true
            );

            _scanTracksEntry.OnValueChanged.Subscribe((oldVal, newVal) =>
            {
                if (oldVal == newVal) return;
                RescanTracksFolder();
            });

            _playPauseKeyEntry = _configCategory.CreateEntry(
                "PlayPauseKey",
                "Semicolon",
                "Play/Pause Key",
                "Key name to play or pause playback (e.g. Semicolon, N, Insert, F3)."
            );
            _switchPlaylistKeyEntry = _configCategory.CreateEntry(
                "SwitchPlaylistKey",
                "Apostrophe",
                "Switch Playlist Key",
                "Key name to cycle through your Tracks subfolders and All Playlists (e.g. Apostrophe, N, J, F2)."
            );
            
            _walkman2DVolumeEntry = _configCategory.CreateEntry(
                "Walkman2DVolume",
                1.0f,
                "Headphones Volume",
                "Volume level while wearing headphones (0.0 to 1.5)."
            );
            _walkman2DVolumeEntry.OnValueChanged.Subscribe((oldVal, newVal) =>
            {
                float clamped = Mathf.Clamp(newVal, 0.0f, 1.5f);
                if (_standalone2DEvent.isValid())
                {
                    _standalone2DEvent.setVolume(clamped);
                    IntPtr chPtr;
                    if (_instanceToChannelMap.TryGetValue(_standalone2DEvent.handle, out chPtr) && chPtr != IntPtr.Zero)
                    {
                        FMOD_Channel_SetVolume(chPtr, _currentFadeMultiplier * clamped * 0.60f);
                    }
                }
            });
            _boombox2DAudioEntry = _configCategory.CreateEntry(
                "Boombox2DAudio",
                false,
                "Wear Headphones",
                "Toggle ON to wear headphones and listen anywhere, or OFF for 3D boomboxes and golf carts."
            );
            _boombox2DAudioEntry.OnValueChanged.Subscribe((oldVal, newVal) =>
            {
                if (oldVal == newVal) return;
                SyncVolumeModRadius(newVal);
                bool wasAnyPlaying = false;

                if (_standalone2DEvent.isValid())
                {
                    if (!_isStandalone2DPaused) wasAnyPlaying = true;
                    SavePlaybackBookmark(_standalone2DEvent, "ModeSwitch2DTo3D", _isStandalone2DPaused);
                    if (Mp3Files.Count > 0)
                    {
                        _currentTrackIndex = _lastPlayedTrackIndex % Mp3Files.Count;
                    }
                }
                StopStandalone2DEvent();
                _pending2DAutoResume = false;

                for (int i = ActiveBoomboxes.Count - 1; i >= 0; i--)
                {
                    Radio r = ActiveBoomboxes[i];
                    if (r == null) continue;

                    var rState = GetOrCreateState(r.GetInstanceID());
                    rState.LastRangeCheckTime = 0f;
                    rState.LastSyncTime = 0f;
                    rState.LastRestartTime = 0f;
                    rState.LastStartRequestTime = 0f;

                    if (r._playingEvent.isValid())
                    {
                        if (r._isOn && !r._isBroken && r._isEventPlaying) wasAnyPlaying = true;
                        SavePlaybackBookmark(r._playingEvent, "ModeSwitchBoomboxTo2D", false);
                        IntPtr oldHandle = r._playingEvent.handle;
                        r._playingEvent.stop(FMOD.Studio.STOP_MODE.IMMEDIATE);
                        r._playingEvent.release();
                        r._playingEvent = default(EventInstance);
                        ReleaseSoundForInstance(oldHandle);
                    }

                    if (!newVal && r._isOn && !r._isBroken && r._isEventPlaying)
                    {
                        rState.NeedsModeRestart = true;
                    }
                }

                for (int i = ActiveRadioPlayers.Count - 1; i >= 0; i--)
                {
                    RadioPlayer rp = ActiveRadioPlayers[i];
                    if (rp == null) continue;
                    var rpState = GetOrCreateState(rp.GetInstanceID());
                    EventInstance cartEvt = rp._playingEvent.isValid() ? rp._playingEvent : rpState.LastPlayingEvent;
                    if (cartEvt.isValid())
                    {
                        if (rp._isOn || rpState.WasOn) wasAnyPlaying = true;
                        SavePlaybackBookmark(cartEvt, "ModeSwitchCartTo2D", false);
                        IntPtr oldHandle = cartEvt.handle;
                        cartEvt.stop(FMOD.Studio.STOP_MODE.IMMEDIATE);
                        cartEvt.release();
                        rp._playingEvent = default(EventInstance);
                        rpState.LastPlayingEvent = default(EventInstance);
                        ReleaseSoundForInstance(oldHandle);
                    }
                }

                if (newVal && wasAnyPlaying)
                {
                    _pending2DAutoResume = true;
                }
            });

            _volumeUpKeyEntry = _configCategory.CreateEntry(
                "VolumeUpKey",
                "Add",
                "Volume Up Key",
                "Key name to increase volume (e.g. Add, Subtract, RightBracket, UpArrow, PageUp). Automatically disabled if sotfVolumeMod is installed."
            );
            _volumeDownKeyEntry = _configCategory.CreateEntry(
                "VolumeDownKey",
                "Subtract",
                "Volume Down Key",
                "Key name to decrease volume (e.g. Subtract, LeftBracket, DownArrow, PageDown). Automatically disabled if sotfVolumeMod is installed."
            );
            _volumeStepPercentEntry = _configCategory.CreateEntry(
                "VolumeStepPercent",
                "25",
                "Volume Step (%)",
                "Percentage increment per volume step (e.g. 5, 10, 25). Automatically disabled if sotfVolumeMod is installed."
            );

            ApplyActivePlaylistSelection("All Playlists");
            if (!File.Exists(customConfigPath))
            {
                _configCategory.SaveToFile(false);
            }
            SettingsRegistry.CreateSettings(this, _configCategory, typeof(CustomRadioMod));
            CheckExternalVolumeModConflicts();
            if (IsBoombox2DEnabled())
            {
                SyncVolumeModRadius(true);
            }


        }

        private static object ReadEntryValue(object entry)
        {
            if (entry == null) return null;
            PropertyInfo prop = entry.GetType().GetProperty("Value");
            return prop != null ? prop.GetValue(entry) : null;
        }
        private static string GetStringConfigValue(object entry, string fallback)
        {
            string val = ReadEntryValue(entry) as string;
            if (!string.IsNullOrWhiteSpace(val))
            {
                return val;
            }
            return fallback;
        }
        private static float GetMaxControlRadius()
        {
            object val = ReadEntryValue(_controlRadiusEntry);
            if (val is float)
            {
                return Mathf.Max(0.5f, (float)val);
            }
            return 10.0f;
        }
        private static FieldInfo _volumeModIgnoreField = null;
        private static Type _externalVolumeModType = null;
        private static bool _externalVolumeModChecked = false;
        private static FieldInfo _extVolUpEntryField = null;
        private static FieldInfo _extVolDownEntryField = null;
        private static readonly HashSet<string> _loggedKeyCollisions = new HashSet<string>(StringComparer.OrdinalIgnoreCase);

        private static Type GetExternalVolumeModType()
        {
            if (!_externalVolumeModChecked)
            {
                _externalVolumeModChecked = true;
                try
                {
                    foreach (var alc in System.Runtime.Loader.AssemblyLoadContext.All)
                    {
                        foreach (Assembly asm in alc.Assemblies)
                        {
                            Type volType = asm.GetType("sotfVolumeMod.RadioVolumeController");
                            if (volType != null)
                            {
                                _externalVolumeModType = volType;
                                break;
                            }
                        }
                        if (_externalVolumeModType != null) break;
                    }
                }
                catch { }
            }
            return _externalVolumeModType;
        }

        public static bool IsSotfVolumeModInstalled()
        {
            return GetExternalVolumeModType() != null;
        }

        private static void GetExternalVolumeModReservedVKeys(out int extUpVKey, out int extDownVKey)
        {
            extUpVKey = 0;
            extDownVKey = 0;
            Type volType = GetExternalVolumeModType();
            if (volType == null) return;
            try
            {
                if (_extVolUpEntryField == null)
                    _extVolUpEntryField = volType.GetField("_volumeUpKey", BindingFlags.Public | BindingFlags.Static);
                if (_extVolDownEntryField == null)
                    _extVolDownEntryField = volType.GetField("_volumeDownKey", BindingFlags.Public | BindingFlags.Static);

                object upEntry = _extVolUpEntryField?.GetValue(null);
                object downEntry = _extVolDownEntryField?.GetValue(null);
                string upStr = ReadEntryValue(upEntry) as string;
                string downStr = ReadEntryValue(downEntry) as string;

                if (!string.IsNullOrWhiteSpace(upStr)) extUpVKey = ResolveVirtualKey(upStr);
                if (!string.IsNullOrWhiteSpace(downStr)) extDownVKey = ResolveVirtualKey(downStr);
            }
            catch { }
        }

        private static void CheckExternalVolumeModConflicts()
        {
            if (!IsSotfVolumeModInstalled()) return;
            int extUp, extDown;
            GetExternalVolumeModReservedVKeys(out extUp, out extDown);
            var checks = new (string name, string keyStr)[]
            {
                ("Play/Pause", GetStringConfigValue(_playPauseKeyEntry, "Semicolon")),
                ("Switch Playlist", GetStringConfigValue(_switchPlaylistKeyEntry, "Apostrophe")),
                ("Skip Track", GetStringConfigValue(_skipKeyEntry, "Backslash")),
                ("Previous Track", GetStringConfigValue(_previousKeyEntry, "P")),
                ("Fast Forward", GetStringConfigValue(_fastForwardKeyEntry, "RightArrow")),
                ("Rewind", GetStringConfigValue(_rewindKeyEntry, "LeftArrow")),
                ("Repeat Track", GetStringConfigValue(_repeatKeyEntry, "O")),
                ("Shuffle", GetStringConfigValue(_shuffleKeyEntry, "K"))
            };
            for (int i = 0; i < checks.Length; i++)
            {
                int vk = ResolveVirtualKey(checks[i].keyStr);
                if (vk != 0 && (vk == extUp || vk == extDown))
                {
                    if (_loggedKeyCollisions.Add(checks[i].name))
                    {
                        RLog.Warning($"mp3player: '{checks[i].name}' key ({checks[i].keyStr}) conflicts with sotfVolumeMod and will be suppressed so sotfVolumeMod can control volume.");
                    }
                }
            }
        }

        private static void SyncVolumeModRadius(bool is2DEnabled)
        {
            try
            {
                if (_volumeModIgnoreField == null)
                {
                    foreach (var alc in System.Runtime.Loader.AssemblyLoadContext.All)
                    {
                        foreach (Assembly asm in alc.Assemblies)
                        {
                            System.Type volType = asm.GetType("sotfVolumeMod.RadioVolumeController");
                            if (volType != null)
                            {
                                _volumeModIgnoreField = volType.GetField("IgnoreControlRadius", BindingFlags.Public | BindingFlags.Static);
                                break;
                            }
                        }
                        if (_volumeModIgnoreField != null) break;
                    }
                }

                if (_volumeModIgnoreField != null)
                {
                    _volumeModIgnoreField.SetValue(null, is2DEnabled);
                }
            }
            catch (Exception ex)
            {
                RLog.Warning($"mp3player: SyncVolumeModRadius error: {ex.Message}");
            }
        }

        public static bool IsBoombox2DEnabled()
        {
            object val = ReadEntryValue(_boombox2DAudioEntry);
            return val is bool && (bool)val;
        }
        public static bool IsPlayerInActiveWorld()
        {
            return LocalPlayer.Transform != null && GetMainCamera() != null;
        }
        public static bool TryGetDistanceSqToPlayer(Transform speakerTransform, out float distSq)
        {
            distSq = float.MaxValue;
            if (!IsPlayerInActiveWorld() || speakerTransform == null)
            {
                return false;
            }
            Vector3 speakerPos = speakerTransform.position;
            if (speakerPos == Vector3.zero)
            {
                return false;
            }
            Camera cam = GetMainCamera();
            Vector3 listenerPos = cam != null
            ? cam.transform.position
            : LocalPlayer.Transform.position;
            if (listenerPos == Vector3.zero)
            {
                return false;
            }
            distSq = (listenerPos - speakerPos).sqrMagnitude;
            return true;
        }
        private static bool DetectEscapeMenuOpen()
        {
            try
            {
                if (LocalPlayer.IsInInventory)
                {
                    return false;
                }
            }
            catch
            {
            }
            if (Time.timeScale <= 0.001f) return true;
            return false;
        }
        public static bool IsManagedCustomEvent(EventInstance eventInstance)
        {
            if (!eventInstance.isValid()) return false;
            IntPtr h = eventInstance.handle;
            return _activePlayingSounds.ContainsKey(h) || _instanceToSoundMap.ContainsKey(h);
        }
        private static void BuildGlyphStampCache()
        {
            _glyphStampCache.Clear();
            string chars = "0123456789-:";
            int stampW = 5 * GlyphScale + StampPad * 2;
            int stampH = 7 * GlyphScale + StampPad * 2;
            for (int c = 0; c < chars.Length; c++)
            {
                char ch = chars[c];
                byte[] rows = GetGlyph5x7(ch);
                byte[] mask = new byte[stampW * stampH];
                for (int r = 0; r < 7; r++)
                {
                    byte rowBits = rows[r];
                    int pyBase = StampPad + (6 - r) * GlyphScale;
                    for (int col = 0; col < 5; col++)
                    {
                        if ((rowBits & (1 << (4 - col))) != 0)
                        {
                            int pxBase = StampPad + col * GlyphScale;
                            for (int dy = 0; dy < GlyphScale; dy++)
                            {
                                int rowOffset = (pyBase + dy) * stampW;
                                for (int dx = 0; dx < GlyphScale; dx++)
                                {
                                    mask[rowOffset + pxBase + dx] = 1;
                                }
                            }
                        }
                    }
                }
                Color32[] colors = new Color32[stampW * stampH];
                for (int y = 0; y < stampH; y++)
                {
                    int rowOffset = y * stampW;
                    for (int x = 0; x < stampW; x++)
                    {
                        int idx = rowOffset + x;
                        float dither = (Bayer4x4[(y & 3) * 4 + (x & 3)] - 0.5f) * 0.06f;

                        if (mask[idx] == 1)
                        {
                            // Measure distance to nearest outside background pixel to soften sharp 90-degree corners
                            int minOutDistSq = 999;
                            for (int oy = -4; oy <= 4; oy++)
                            {
                                int ny = y + oy;
                                int oySq = oy * oy;
                                for (int ox = -4; ox <= 4; ox++)
                                {
                                    int nx = x + ox;
                                    bool isOut = (ny < 0 || ny >= stampH || nx < 0 || nx >= stampW || mask[ny * stampW + nx] == 0);
                                    if (isOut)
                                    {
                                        int dSq = oySq + ox * ox;
                                        if (dSq < minOutDistSq) minOutDistSq = dSq;
                                    }
                                }
                            }
                            float innerDist = (float)Math.Sqrt(minOutDistSq);
                            float innerAlpha = Math.Min(1.0f, 0.72f + (innerDist / 4.2f) * 0.28f + dither * 0.5f);
                            colors[idx] = Color32.Lerp(LcdBgColor32, LcdFgColor32, Math.Max(0f, innerAlpha));
                            continue;
                        }

                        int minDistSq = 999;
                        for (int oy = -6; oy <= 6; oy++)
                        {
                            int ny = y + oy;
                            if (ny < 0 || ny >= stampH) continue;
                            int nRow = ny * stampW;
                            int oySq = oy * oy;
                            for (int ox = -6; ox <= 6; ox++)
                            {
                                int nx = x + ox;
                                if (nx >= 0 && nx < stampW && mask[nRow + nx] == 1)
                                {
                                    int dSq = oySq + ox * ox;
                                    if (dSq < minDistSq) minDistSq = dSq;
                                }
                            }
                        }

                        if (minDistSq <= 36)
                        {
                            float dist = (float)Math.Sqrt(minDistSq);
                            float t = Math.Max(0f, 1.0f - (dist / 6.2f));
                            // Smooth cubic curve + subtle Bayer dithering for a soft LCD glow
                            float alpha = (t * t * (3.0f - 2.0f * t)) * 0.78f + dither;
                            alpha = Math.Max(0f, Math.Min(1f, alpha));
                            colors[idx] = Color32.Lerp(LcdBgColor32, LcdFgColor32, alpha);
                        }
                        else
                        {
                            colors[idx] = LcdBgColor32;
                        }
                    }
                }

                _glyphStampCache[ch] = colors;
            }
        }
        private static void FillBufferBackground(Color32[] buffer)
        {
            for (int i = 0; i < buffer.Length; i++)
            {
                buffer[i] = LcdBgColor32;
            }
        }
        public static void UpdateBoomboxLcd(Radio radio, RadioRuntimeState radioState, EventInstance playingEvent, bool isActive)
        {
            try
            {
                if (radio == null) return;
                if (!isActive || !playingEvent.isValid() || Mp3Files.Count == 0)
                {
                    if (radioState.LcdState != null)
                    {
                        radioState.LcdState.LastDisplayedText = "";
                        radioState.LcdState.NextPollTime = 0f;
                        if (radioState.LcdState.RootObj != null && radioState.LcdState.RootObj.activeSelf)
                        {
                            radioState.LcdState.RootObj.SetActive(false);
                        }
                    }
                    return;
                }
                BoomboxWorldLcdState state = radioState.LcdState;
                if (state == null)
                {
                    state = CreateReplacementBoomboxScreen(radio);
                    radioState.LcdState = state;
                }
                if (state.Failed || state.RootObj == null || state.LcdTex == null || state.PixelBuffer == null)
                {
                    return;
                }
                float now = Time.realtimeSinceStartup;
                if (now < state.NextPollTime)
                {
                    return;
                }
                state.NextPollTime = now + 0.25f;
                if (!state.RootObj.activeSelf)
                {
                    state.RootObj.SetActive(true);
                }
                PlaybackTimerState timerState;
                if (!_instanceTimerStates.TryGetValue(playingEvent.handle, out timerState) || !timerState.ChannelAnchored)
                {
                    return;
                }
                float elapsedSec = radioState.IsUserPaused ? 0f : Math.Max(0f, now - timerState.AnchorRealtime);
                uint currentPosMs = timerState.AnchorPositionMs + (uint)(elapsedSec * 1000f);
                uint remainingMs = timerState.TotalLengthMs > currentPosMs ? (timerState.TotalLengthMs - currentPosMs) : 0;
                string formatted = FormatTimeMs(remainingMs);
                if (formatted != state.LastDisplayedText)
                {
                    string prevText = state.LastDisplayedText;
                    state.LastDisplayedText = formatted;
                    RenderLcdPixelBuffer(state, formatted, prevText);
                }
            }
            catch (Exception ex)
            {
                RLog.Warning($"mp3player: Replacement LCD error: {ex.Message}");
            }
        }
        private static BoomboxWorldLcdState CreateReplacementBoomboxScreen(Radio radio)
        {
            var state = new BoomboxWorldLcdState();
            try
            {
                var rootObj = new GameObject("CustomBoomboxWorldLcdRoot");

                var tex = new Texture2D(LcdTexWidth, LcdTexHeight, TextureFormat.RGBA32, false);
                tex.filterMode = FilterMode.Bilinear;
                tex.anisoLevel = 8;
                tex.wrapMode = TextureWrapMode.Clamp;
                state.LcdTex = tex;

                var buffer = new Color32[LcdTexWidth * LcdTexHeight];
                state.PixelBuffer = buffer;
                state.BufferPinHandle = GCHandle.Alloc(buffer, GCHandleType.Pinned);
                state.IsBufferPinned = true;

                FillBufferBackground(buffer);
                state.UploadBufferToTexture();
                RenderLcdPixelBuffer(state, "00:00", "");

                var canvas = rootObj.AddComponent<UnityEngine.Canvas>();
                canvas.renderMode = RenderMode.WorldSpace;
                canvas.sortingOrder = 50;

                rootObj.transform.SetParent(radio.transform, false);
                rootObj.transform.localPosition = new Vector3(_livePosX, _livePosY + 0.036f, _livePosZ + 0.002f);
                rootObj.transform.localEulerAngles = new Vector3(0f, _liveRotY + 180f, 0f);
                rootObj.transform.localScale = new Vector3(_liveScaleX, _liveScaleY, _liveScaleX);

                // Front screen face
                var frontObj = new GameObject("LcdFrontFace");
                frontObj.transform.SetParent(rootObj.transform, false);
                var frontRect = frontObj.AddComponent<RectTransform>();
                frontRect.anchorMin = new Vector2(0.5f, 0.5f);
                frontRect.anchorMax = new Vector2(0.5f, 0.5f);
                frontRect.pivot = new Vector2(0.5f, 0.5f);
                frontRect.sizeDelta = new Vector2(100f, 100f);

                frontRect.localPosition = Vector3.zero;
                frontRect.localEulerAngles = Vector3.zero;
                frontRect.localScale = Vector3.one;

                var frontImg = frontObj.AddComponent<UnityEngine.UI.RawImage>();
                frontImg.texture = tex;
                frontImg.color = Color.white;

                state.RootObj = rootObj;
            }
            catch (Exception ex)
            {
                state.Failed = true;
                state.CleanupAssets();
                RLog.Warning($"mp3player: CreateReplacementBoomboxScreen failed: {ex.Message}");
            }
            return state;
        }

        private static void RenderLcdPixelBuffer(BoomboxWorldLcdState state, string text, string previousText)
        {
            Color32[] buffer = state.PixelBuffer;
            bool lengthChanged = previousText.Length != text.Length;
            if (lengthChanged)
            {
                FillBufferBackground(buffer);
            }
            int glyphW = 5 * GlyphScale;
            int glyphH = 7 * GlyphScale;
            int stampW = glyphW + StampPad * 2;
            int stampH = glyphH + StampPad * 2;
            int totalW = text.Length * glyphW + Math.Max(0, text.Length - 1) * GlyphSpacing;
            int startX = Math.Max(6, (LcdTexWidth - totalW) / 2);
            int startY = Math.Max(6, (LcdTexHeight - glyphH) / 2);
            bool anyUpdated = lengthChanged;
            for (int cIdx = 0; cIdx < text.Length; cIdx++)
            {
                char ch = text[cIdx];
                if (!lengthChanged && cIdx < previousText.Length && previousText[cIdx] == ch)
                {
                    continue;
                }
                Color32[] stampColors;
                if (!_glyphStampCache.TryGetValue(ch, out stampColors))
                {
                    continue;
                }
                int destX = startX + cIdx * (glyphW + GlyphSpacing) - StampPad;
                int destY = startY - StampPad;
                if (destX < 0 || destY < 0 || destX + stampW > LcdTexWidth || destY + stampH > LcdTexHeight)
                {
                    continue;
                }
                for (int sy = 0; sy < stampH; sy++)
                {
                    int srcOffset = sy * stampW;
                    int dstOffset = (destY + sy) * LcdTexWidth + destX;
                    Array.Copy(stampColors, srcOffset, buffer, dstOffset, stampW);
                }
                anyUpdated = true;
            }
            if (anyUpdated)
            {
                state.UploadBufferToTexture();
            }
        }
        private static byte[] GetGlyph5x7(char c)
        {
            switch (c)
            {
                case '0': return new byte[] { 0x0E, 0x11, 0x13, 0x15, 0x19, 0x11, 0x0E };
                case '1': return new byte[] { 0x04, 0x0C, 0x04, 0x04, 0x04, 0x04, 0x0E };
                case '2': return new byte[] { 0x0E, 0x11, 0x01, 0x06, 0x08, 0x10, 0x1F };
                case '3': return new byte[] { 0x1E, 0x01, 0x01, 0x0E, 0x01, 0x01, 0x1E };
                case '4': return new byte[] { 0x02, 0x06, 0x0A, 0x12, 0x1F, 0x02, 0x02 };
                case '5': return new byte[] { 0x1F, 0x10, 0x1E, 0x01, 0x01, 0x11, 0x0E };
                case '6': return new byte[] { 0x06, 0x08, 0x10, 0x1E, 0x11, 0x11, 0x0E };
                case '7': return new byte[] { 0x1F, 0x01, 0x02, 0x04, 0x08, 0x08, 0x08 };
                case '8': return new byte[] { 0x0E, 0x11, 0x11, 0x0E, 0x11, 0x11, 0x0E };
                case '9': return new byte[] { 0x0E, 0x11, 0x11, 0x0F, 0x01, 0x02, 0x0C };
                case '-': return new byte[] { 0x00, 0x00, 0x00, 0x1F, 0x00, 0x00, 0x00 };
                case ':': return new byte[] { 0x00, 0x04, 0x04, 0x00, 0x04, 0x04, 0x00 };
                default: return new byte[] { 0, 0, 0, 0, 0, 0, 0 };
            }
        }
        private static void EnsureHudCreated()
        {
            if (_hudCanvasObj != null) return;
            _hudCanvasObj = new GameObject("MP3PlayerHudCanvas");
            UnityEngine.Object.DontDestroyOnLoad(_hudCanvasObj);
            var canvas = _hudCanvasObj.AddComponent<UnityEngine.Canvas>();
            canvas.renderMode = RenderMode.ScreenSpaceOverlay;
            canvas.sortingOrder = 999;
            var scaler = _hudCanvasObj.AddComponent<UnityEngine.UI.CanvasScaler>();
            scaler.uiScaleMode = UnityEngine.UI.CanvasScaler.ScaleMode.ScaleWithScreenSize;
            scaler.referenceResolution = new Vector2(1920f, 1080f);
            _hudBoxObj = new GameObject("NowPlayingBox");
            _hudBoxObj.transform.SetParent(_hudCanvasObj.transform, false);
            var boxRect = _hudBoxObj.AddComponent<UnityEngine.RectTransform>();
            boxRect.anchorMin = new Vector2(0.5f, 0f);
            boxRect.anchorMax = new Vector2(0.5f, 0f);
            boxRect.pivot = new Vector2(0.5f, 0f);
            boxRect.anchoredPosition = new Vector2(0f, 135f);
            boxRect.sizeDelta = new Vector2(460f, 44f);
            var bgImage = _hudBoxObj.AddComponent<UnityEngine.UI.Image>();
            bgImage.color = new Color(0.06f, 0.06f, 0.08f, 0.82f);
            _hudBoxObj.AddComponent<UnityEngine.UI.RectMask2D>();
            var layout = _hudBoxObj.AddComponent<UnityEngine.UI.HorizontalLayoutGroup>();
            layout.childAlignment = TextAnchor.MiddleLeft;
            layout.padding = new RectOffset(14, 14, 4, 4);
            layout.spacing = 6f;
            layout.childControlWidth = true;
            layout.childControlHeight = true;
            layout.childForceExpandWidth = false;
            layout.childForceExpandHeight = true;
            UnityEngine.Font arialFont = Resources.GetBuiltinResource<UnityEngine.Font>("Arial.ttf");
            var prefixObj = new GameObject("NowPlayingPrefix");
            prefixObj.transform.SetParent(_hudBoxObj.transform, false);
            var prefixLayout = prefixObj.AddComponent<UnityEngine.UI.LayoutElement>();
            prefixLayout.flexibleWidth = 0f;
            _hudPrefixLabel = prefixObj.AddComponent<UnityEngine.UI.Text>();
            _hudPrefixLabel.font = arialFont;
            _hudPrefixLabel.fontSize = 18;
            _hudPrefixLabel.fontStyle = FontStyle.Bold;
            _hudPrefixLabel.alignment = TextAnchor.MiddleLeft;
            _hudPrefixLabel.color = Color.white;
            _hudPrefixLabel.supportRichText = false;
            _hudPrefixLabel.horizontalOverflow = HorizontalWrapMode.Overflow;
            _hudPrefixLabel.verticalOverflow = VerticalWrapMode.Overflow;
            var clipObj = new GameObject("NowPlayingClip");
            clipObj.transform.SetParent(_hudBoxObj.transform, false);
            var clipLayout = clipObj.AddComponent<UnityEngine.UI.LayoutElement>();
            clipLayout.flexibleWidth = 1f;
            clipLayout.minWidth = 40f;
            clipObj.AddComponent<UnityEngine.UI.RectMask2D>();
            var valueObj = new GameObject("NowPlayingValue");
            valueObj.transform.SetParent(clipObj.transform, false);
            _hudValueRect = valueObj.AddComponent<RectTransform>();
            _hudValueRect.anchorMin = new Vector2(0f, 0f);
            _hudValueRect.anchorMax = new Vector2(0f, 1f);
            _hudValueRect.pivot = new Vector2(0f, 0.5f);
            _hudValueRect.anchoredPosition = Vector2.zero;
            var valueFitter = valueObj.AddComponent<UnityEngine.UI.ContentSizeFitter>();
            valueFitter.horizontalFit = UnityEngine.UI.ContentSizeFitter.FitMode.PreferredSize;
            valueFitter.verticalFit = UnityEngine.UI.ContentSizeFitter.FitMode.Unconstrained;
            _hudValueLabel = valueObj.AddComponent<UnityEngine.UI.Text>();
            _hudValueLabel.font = arialFont;
            _hudValueLabel.fontSize = 18;
            _hudValueLabel.fontStyle = FontStyle.Bold;
            _hudValueLabel.alignment = TextAnchor.MiddleLeft;
            _hudValueLabel.color = new Color(0.40f, 0.85f, 1.00f, 1.00f);
            _hudValueLabel.supportRichText = false;
            _hudValueLabel.horizontalOverflow = HorizontalWrapMode.Overflow;
            _hudValueLabel.verticalOverflow = VerticalWrapMode.Overflow;
            _hudBoxObj.SetActive(false);
        }
        private static string BuildTrackHudPrefix(string trackPath, string rootFallbackLabel)
        {
            if (_playlistNames.Count <= 1 || string.IsNullOrEmpty(_modFolder) || string.IsNullOrEmpty(trackPath))
            {
                return rootFallbackLabel;
            }
            string activePlaylist = _playlistNames[_currentPlaylistIndex];
            if (activePlaylist.Equals("Root", StringComparison.OrdinalIgnoreCase))
            {
                return rootFallbackLabel;
            }
            if (activePlaylist.Equals("All Playlists", StringComparison.OrdinalIgnoreCase))
            {
                string tracksRoot = Path.GetFullPath(Path.Combine(_modFolder, "Tracks")).TrimEnd(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar);
                string parentDir = Path.GetFullPath(Path.GetDirectoryName(trackPath) ?? "").TrimEnd(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar);
                if (!string.IsNullOrEmpty(parentDir) && !parentDir.Equals(tracksRoot, StringComparison.OrdinalIgnoreCase))
                {
                    string folderName = Path.GetFileName(parentDir);
                    if (!string.IsNullOrEmpty(folderName))
                    {
                        return $"All Playlists:{folderName}";
                    }
                }
                return "All Playlists:Root";
            }
            return activePlaylist;
        }
        private static void ShowHudMessage(string prefix, string highlightText)
        {
            if (!IsPlayerInActiveWorld()) return;
            EnsureHudCreated();
            if (_hudBoxObj != null && _hudPrefixLabel != null && _hudValueLabel != null && _hudValueRect != null)
            {
                _hudBoxObj.SetActive(true);
                _hudPrefixLabel.text = $"{prefix}:";
                var prefixLayout = _hudPrefixLabel.GetComponent<UnityEngine.UI.LayoutElement>();
                if (prefixLayout != null)
                {
                    prefixLayout.minWidth = Mathf.Min(280f, _hudPrefixLabel.preferredWidth);
                }
                _hudValueLabel.text = highlightText;
                var boxRect = _hudBoxObj.GetComponent<RectTransform>();
                if (boxRect != null)
                {
                    UnityEngine.UI.LayoutRebuilder.ForceRebuildLayoutImmediate(boxRect);
                }
                _hudValueRect.anchoredPosition = Vector2.zero;
                _hudScrollElapsed = 0f;
                _hudScrollFinished = false;
                var clipRect = _hudValueRect.parent as RectTransform;
                float availableW = clipRect != null ? clipRect.rect.width : 180f;
                float textW = _hudValueLabel.preferredWidth;
                if (textW > availableW + 4f)
                {
                    _hudScrollDistance = textW - availableW + 8f;
                    float scrollTime = _hudScrollDistance / HudScrollSpeed;
                    _hudTimer = HudScrollStartDelay + scrollTime + HudScrollEndHold + 0.85f;
                }
                else
                {
                    _hudScrollDistance = 0f;
                    _hudTimer = HudDuration;
                }
            }
        }
        private static int ResolveVirtualKey(string keyName)
        {
            if (string.IsNullOrWhiteSpace(keyName)) return 0xDC;
            string clean = keyName.Trim();
            int numericCode;
            if (int.TryParse(clean, out numericCode)) return numericCode;
            if (clean.Length == 1)
            {
                char c = char.Parse(clean.ToUpperInvariant());
                if ((c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')) return c;
            }
            switch (clean.ToLowerInvariant())
            {
                case "add":
                case "numpadplus":
                case "keypadplus":
                case "numpad+":
                case "plus": return 0x6B;
                case "subtract":
                case "numpadminus":
                case "keypadminus":
                case "numpad-":
                case "minus": return 0x6D;
                case "equals":
                case "oem_plus": return 0xBB;
                case "oem_minus": return 0xBD;
                case "rightbracket": return 0xDD;
                case "leftbracket": return 0xDB;
                case "backslash": return 0xDC;
                case "semicolon": return 0xBA;
                case "apostrophe": return 0xDE;
                case "pagedown": return 0x22;
                case "pageup": return 0x21;
                case "rightarrow":
                case "right": return 0x27;
                case "leftarrow":
                case "left": return 0x25;
                case "uparrow":
                case "up": return 0x26;
                case "downarrow":
                case "down": return 0x28;
                case "insert": return 0x2D;
                case "delete": return 0x2E;
                case "home": return 0x24;
                case "end": return 0x23;
                case "f1": return 0x70;
                case "f2": return 0x71;
                case "f3": return 0x72;
                case "f4": return 0x73;
                case "f5": return 0x74;
                case "f6": return 0x75;
                case "f7": return 0x76;
                case "f8": return 0x77;
                case "f9": return 0x78;
                case "f10": return 0x79;
                case "f11": return 0x7A;
                case "f12": return 0x7B;
                default: return 0xDC;
            }
        }
        private static void ResetKeyStates()
        {
            _wasPlayPauseKeyDown = false;
            _wasSwitchPlaylistKeyDown = false;
            _wasSkipKeyDown = false;
            _wasPreviousKeyDown = false;
            _wasFastForwardKeyDown = false;
            _wasRewindKeyDown = false;
            _wasRepeatKeyDown = false;
            _wasShuffleKeyDown = false;
            _wasVolUpKeyDown = false;
            _wasVolDownKeyDown = false;
            _volumeHoldTimer = 0f;
        }
        private static void StartStandalone2DTrack(bool showHud = true)
        {
            if (!IsFmodReady || Mp3Files.Count == 0 || !IsPlayerInActiveWorld()) return;
            StopStandalone2DEvent();
            float vol = GetWalkman2DVolume();
            var inst = CreateCustomStreamInstance(LocalPlayer.Transform, vol, showHud: showHud, is2D: true);
            if (!inst.isValid()) return;
            _standalone2DEvent = inst;
            _isStandalone2DPaused = false;
            PlaybackTimerState timerState;
            if (_instanceTimerStates.TryGetValue(inst.handle, out timerState) && timerState.TotalLengthMs > 0)
            {
                _standalone2DEndTime = Time.realtimeSinceStartup + (timerState.TotalLengthMs / 1000f) + 0.35f;
            }
            else
            {
                _standalone2DEndTime = float.MaxValue;
            }
        }
        private static void ToggleStandalone2DPlayPause()
        {
            if (!IsFmodReady || Mp3Files.Count == 0) return;
            float now = Time.realtimeSinceStartup;
            if (!_standalone2DEvent.isValid())
            {
                if (_savedPositionMs > 0)
                {
                    _resumeSavedPositionOnNextStart = true;
                }
                ForceSkipRequested = true;
                StartStandalone2DTrack(showHud: true);
                ForceSkipRequested = false;
                return;
            }
            PlaybackTimerState timerState;
            _instanceTimerStates.TryGetValue(_standalone2DEvent.handle, out timerState);
            string title = Mp3Files.Count > 0 ? Path.GetFileNameWithoutExtension(Mp3Files[_lastPlayedTrackIndex % Mp3Files.Count]) : "Track";
            if (!_isStandalone2DPaused)
            {
                _isStandalone2DPaused = true;
                _standalone2DEvent.setPaused(true);
                if (timerState != null && timerState.ChannelAnchored)
                {
                    float elapsedSec = Math.Max(0f, now - timerState.AnchorRealtime);
                    timerState.AnchorPositionMs += (uint)(elapsedSec * 1000f);
                    timerState.AnchorRealtime = now;
                }
                _standalone2DEndTime = float.MaxValue;
                ShowHudMessage("Paused", title);
            }
            else
            {
                _isStandalone2DPaused = false;
                _standalone2DEvent.setPaused(false);
                if (timerState != null)
                {
                    timerState.AnchorRealtime = now;
                    if (timerState.TotalLengthMs > 0)
                    {
                        uint remMs = timerState.TotalLengthMs > timerState.AnchorPositionMs
                            ? (timerState.TotalLengthMs - timerState.AnchorPositionMs)
                            : 0;
                        _standalone2DEndTime = now + (remMs / 1000f) + 0.35f;
                    }
                }
                ShowHudMessage("Resumed", title);
            }
        }
        private void HandleUpdate()
        {
            if (!IsPlayerInActiveWorld())
            {
                StopStandalone2DEvent();
                ClearPlaybackBookmark();
                _pending2DAutoResume = false;
                _worldReadyTime = -1f;
                _isEscapeMenuOpen = false;
                _cachedMainCamera = null;
                foreach (var kvp in _radioStates)
                {
                    if (kvp.Value.LcdState != null)
                    {
                        kvp.Value.LcdState.CleanupAssets();
                    }
                }
                _radioStates.Clear();
                ResetKeyStates();
                if (_hudBoxObj != null && _hudBoxObj.activeSelf)
                {
                    _hudBoxObj.SetActive(false);
                    _hudTimer = 0f;
                }
                return;
            }
            float now = Time.realtimeSinceStartup;
            if (_worldReadyTime < 0f)
            {
                _worldReadyTime = now;
                SyncVolumeModRadius(IsBoombox2DEnabled());
            }
            if ((now - _lastWindowFocusCheckTime) >= 0.1f)
            {
                _lastWindowFocusCheckTime = now;
                _isWindowForeground = QueryWindowForeground();
            }
            _isEscapeMenuOpen = DetectEscapeMenuOpen();
            bool shouldMute = !_isWindowForeground || _isEscapeMenuOpen;
            if (_hudTimer > 0f)
            {
                float dt = Time.unscaledDeltaTime;
                _hudTimer -= dt;
                if (_hudScrollDistance > 0f && _hudValueRect != null && !_hudScrollFinished)
                {
                    _hudScrollElapsed += dt;
                    float scrollDuration = _hudScrollDistance / HudScrollSpeed;
                    if (_hudScrollElapsed <= HudScrollStartDelay)
                    {
                        _hudValueRect.anchoredPosition = Vector2.zero;
                    }
                    else if (_hudScrollElapsed <= HudScrollStartDelay + scrollDuration)
                    {
                        float offset = (_hudScrollElapsed - HudScrollStartDelay) * HudScrollSpeed;
                        _hudValueRect.anchoredPosition = new Vector2(-offset, 0f);
                    }
                    else if (_hudScrollElapsed <= HudScrollStartDelay + scrollDuration + HudScrollEndHold)
                    {
                        _hudValueRect.anchoredPosition = new Vector2(-_hudScrollDistance, 0f);
                    }
                    else
                    {
                        _hudValueRect.anchoredPosition = Vector2.zero;
                        _hudScrollFinished = true;
                    }
                }
                if (_hudTimer <= 0f && _hudBoxObj != null && _hudBoxObj.activeSelf)
                {
                    _hudBoxObj.SetActive(false);
                }
            }
            for (int i = ActiveRadioPlayers.Count - 1; i >= 0; i--)
            {
                RadioPlayer rp = ActiveRadioPlayers[i];
                if (rp == null)
                {
                    ActiveRadioPlayers.RemoveAt(i);
                    continue;
                }
                var rpState = GetOrCreateState(rp.GetInstanceID());
                EventInstance activeRpEvt = rp._playingEvent.isValid() ? rp._playingEvent : rpState.LastPlayingEvent;
                if (!rp._isOn)
                {
                    if (rpState.WasOn && activeRpEvt.isValid())
                    {
                        if (!IsBoombox2DEnabled() && IsManagedCustomEvent(activeRpEvt))
                        {
                            SavePlaybackBookmark(activeRpEvt, "GolfCartOff");
                        }
                        IntPtr stopHandle = activeRpEvt.handle;
                        activeRpEvt.stop(FMOD.Studio.STOP_MODE.IMMEDIATE);
                        activeRpEvt.release();
                        rp._playingEvent = default(EventInstance);
                        rpState.LastPlayingEvent = default(EventInstance);
                        ReleaseSoundForInstance(stopHandle);
                    }
                    rpState.WasOn = false;
                    rpState.IsUserPaused = false;
                    rpState.LastPlayingEvent = default(EventInstance);
                    continue;
                }
                rpState.WasOn = true;
                if (!activeRpEvt.isValid()) continue;

                if (IsManagedCustomEvent(activeRpEvt))
                {
                    rpState.LastPlayingEvent = activeRpEvt;
                }
                RegisterActiveChannelForInstance(activeRpEvt.handle, rpState, now);
                if (_savedPositionMs > 0 && IsChannelRegistered(activeRpEvt.handle) && (now - rpState.LastStartRequestTime) > 1.5f)
                {
                    _savedPositionMs = 0;
                }

                rp._eventLengthSec = 99999;
                if (rpState.IsUserPaused) continue;

                if ((now - rpState.LastFinishCheckTime) >= 0.50f)
                {
                    rpState.LastFinishCheckTime = now;
                    if (HasTrackFinished(activeRpEvt, now) || IsSilentStalledStream(activeRpEvt, now))
                    {
                        if ((now - rpState.LastRestartTime) > 3.5f)
                        {
                            rpState.LastRestartTime = now;
                            ForceSkipRequested = true;
                            IsNaturalAutoAdvance = true;
                            rp.StartEvent("");
                            IsNaturalAutoAdvance = false;
                            ForceSkipRequested = false;
                        }
                    }
                }
            }

            for (int i = ActiveBoomboxes.Count - 1; i >= 0; i--)
            {
                Radio r = ActiveBoomboxes[i];
                if (r == null || !r.gameObject.activeInHierarchy)
                {
                    ActiveBoomboxes.RemoveAt(i);
                    continue;
                }
                RadioRuntimeState rState;
                if (TryGetState(r.GetInstanceID(), out rState) && rState != null)
                {
                    if (r._isOn && !r._isBroken && r._playingEvent.isValid() && IsManagedCustomEvent(r._playingEvent))
                    {
                        rState.LastPlayingEvent = r._playingEvent;
                    }
                    else if (!r._isOn && rState.LastPlayingEvent.isValid())
                    {
                        if (!IsBoombox2DEnabled() && IsManagedCustomEvent(rState.LastPlayingEvent))
                        {
                            SavePlaybackBookmark(rState.LastPlayingEvent, "BoomboxOffBeforePickup");
                        }
                        rState.LastPlayingEvent = default(EventInstance);
                    }
                }
            }
            foreach (var kvp in _radioStates)
            {
                RadioRuntimeState st = kvp.Value;
                if (st != null && st.LastPlayingEvent.isValid())
                {
                    bool stillOwned = false;
                    for (int i = 0; i < ActiveBoomboxes.Count; i++)
                    {
                        Radio r = ActiveBoomboxes[i];
                        if (r != null && r.GetInstanceID() == kvp.Key)
                        {
                            stillOwned = true;
                            break;
                        }
                    }
                    if (!stillOwned)
                    {
                        for (int i = 0; i < ActiveRadioPlayers.Count; i++)
                        {
                            RadioPlayer rp = ActiveRadioPlayers[i];
                            if (rp != null && rp.GetInstanceID() == kvp.Key)
                            {
                                stillOwned = true;
                                break;
                            }
                        }
                    }
                    if (!stillOwned)
                    {
                        if (!IsBoombox2DEnabled() && IsManagedCustomEvent(st.LastPlayingEvent))
                        {
                            SavePlaybackBookmark(st.LastPlayingEvent, "BoomboxDestroyedOnPickup");
                        }
                        IntPtr orphanHandle = st.LastPlayingEvent.handle;
                        st.LastPlayingEvent.stop(FMOD.Studio.STOP_MODE.IMMEDIATE);
                        st.LastPlayingEvent.release();
                        st.LastPlayingEvent = default(EventInstance);
                        ReleaseSoundForInstance(orphanHandle);
                    }
                }
            }

            bool is2DMode = IsBoombox2DEnabled();
            if (is2DMode && _pending2DAutoResume && !shouldMute && IsFmodReady && Mp3Files.Count > 0)
            {
                _pending2DAutoResume = false;
                ForceSkipRequested = true;
                KeepCurrentTrackOnRestart = true;
                SuppressNextHudPopup = true;
                StartStandalone2DTrack(showHud: false);
                SuppressNextHudPopup = false;
                KeepCurrentTrackOnRestart = false;
                ForceSkipRequested = false;
            }
            if (is2DMode && _standalone2DEvent.isValid())
            {
                var walkmanState = GetOrCreateState(-999999);
                RegisterActiveChannelForInstance(_standalone2DEvent.handle, walkmanState, now);
                if (!_isStandalone2DPaused && now >= _standalone2DEndTime && Mp3Files.Count > 0)
                {
                    ClearPlaybackBookmark();
                    ForceSkipRequested = true;
                    IsNaturalAutoAdvance = true;
                    StartStandalone2DTrack(showHud: true);
                    IsNaturalAutoAdvance = false;
                    ForceSkipRequested = false;
                }
            }

            if (shouldMute || Mp3Files.Count == 0)
            {
                ResetKeyStates();
                return;
            }

            Radio nearestBoombox = null;
            RadioPlayer nearestRadioPlayer = null;
            if (!is2DMode)
            {
                if (ActiveBoomboxes.Count == 0 && ActiveRadioPlayers.Count == 0)
                {
                    ResetKeyStates();
                    return;
                }
                FindNearestActiveEvent(out nearestBoombox, out nearestRadioPlayer);
                if (nearestBoombox == null && nearestRadioPlayer == null)
                {
                    ResetKeyStates();
                    return;
                }
            }
            string playPauseStr = GetStringConfigValue(_playPauseKeyEntry, "Semicolon");
            if (playPauseStr != _cachedPlayPauseStr)
            {
                _cachedPlayPauseStr = playPauseStr;
                _cachedPlayPauseVKey = ResolveVirtualKey(_cachedPlayPauseStr);
            }
            string switchPlaylistStr = GetStringConfigValue(_switchPlaylistKeyEntry, "Apostrophe");
            if (switchPlaylistStr != _cachedSwitchPlaylistStr)
            {
                _cachedSwitchPlaylistStr = switchPlaylistStr;
                _cachedSwitchPlaylistVKey = ResolveVirtualKey(_cachedSwitchPlaylistStr);
            }
            string skipStr = GetStringConfigValue(_skipKeyEntry, "Backslash");
            if (skipStr != _cachedSkipStr)
            {
                _cachedSkipStr = skipStr;
                _cachedSkipVKey = ResolveVirtualKey(_cachedSkipStr);
            }
            string prevStr = GetStringConfigValue(_previousKeyEntry, "P");
            if (prevStr != _cachedPrevStr)
            {
                _cachedPrevStr = prevStr;
                _cachedPrevVKey = ResolveVirtualKey(_cachedPrevStr);
            }
            string ffStr = GetStringConfigValue(_fastForwardKeyEntry, "RightArrow");
            if (ffStr != _cachedFfStr)
            {
                _cachedFfStr = ffStr;
                _cachedFfVKey = ResolveVirtualKey(_cachedFfStr);
            }
            string rwStr = GetStringConfigValue(_rewindKeyEntry, "LeftArrow");
            if (rwStr != _cachedRwStr)
            {
                _cachedRwStr = rwStr;
                _cachedRwVKey = ResolveVirtualKey(_cachedRwStr);
            }
            string repeatStr = GetStringConfigValue(_repeatKeyEntry, "O");
            if (repeatStr != _cachedRepeatStr)
            {
                _cachedRepeatStr = repeatStr;
                _cachedRepeatVKey = ResolveVirtualKey(_cachedRepeatStr);
            }
            string shuffleStr = GetStringConfigValue(_shuffleKeyEntry, "K");
            if (shuffleStr != _cachedShuffleStr)
            {
                _cachedShuffleStr = shuffleStr;
                _cachedShuffleVKey = ResolveVirtualKey(_cachedShuffleStr);
            }
            bool isPlayPauseDown = (GetAsyncKeyState(_cachedPlayPauseVKey) & 0x8000) != 0;
            bool isSwitchPlaylistDown = (GetAsyncKeyState(_cachedSwitchPlaylistVKey) & 0x8000) != 0;
            bool isSkipDown = (GetAsyncKeyState(_cachedSkipVKey) & 0x8000) != 0;
            bool isPrevDown = (GetAsyncKeyState(_cachedPrevVKey) & 0x8000) != 0;
            bool isFfDown = (GetAsyncKeyState(_cachedFfVKey) & 0x8000) != 0;
            bool isRwDown = (GetAsyncKeyState(_cachedRwVKey) & 0x8000) != 0;
            bool isRepeatDown = (GetAsyncKeyState(_cachedRepeatVKey) & 0x8000) != 0;
            bool isShuffleDown = (GetAsyncKeyState(_cachedShuffleVKey) & 0x8000) != 0;
            bool extVolInstalled = IsSotfVolumeModInstalled();
            int extUpVKey = 0, extDownVKey = 0;
            if (extVolInstalled)
            {
                GetExternalVolumeModReservedVKeys(out extUpVKey, out extDownVKey);
            }

            bool playPauseTriggered = isPlayPauseDown && !_wasPlayPauseKeyDown && (_cachedPlayPauseVKey != extUpVKey && _cachedPlayPauseVKey != extDownVKey);
            bool switchPlaylistTriggered = isSwitchPlaylistDown && !_wasSwitchPlaylistKeyDown && (_cachedSwitchPlaylistVKey != extUpVKey && _cachedSwitchPlaylistVKey != extDownVKey);
            bool skipTriggered = isSkipDown && !_wasSkipKeyDown && (_cachedSkipVKey != extUpVKey && _cachedSkipVKey != extDownVKey);
            bool prevTriggered = isPrevDown && !_wasPreviousKeyDown && (_cachedPrevVKey != extUpVKey && _cachedPrevVKey != extDownVKey);
            bool ffTriggered = isFfDown && !_wasFastForwardKeyDown && (_cachedFfVKey != extUpVKey && _cachedFfVKey != extDownVKey);
            bool rwTriggered = isRwDown && !_wasRewindKeyDown && (_cachedRwVKey != extUpVKey && _cachedRwVKey != extDownVKey);
            bool repeatTriggered = isRepeatDown && !_wasRepeatKeyDown && (_cachedRepeatVKey != extUpVKey && _cachedRepeatVKey != extDownVKey);
            bool shuffleTriggered = isShuffleDown && !_wasShuffleKeyDown && (_cachedShuffleVKey != extUpVKey && _cachedShuffleVKey != extDownVKey);
            _wasPlayPauseKeyDown = isPlayPauseDown;
            _wasSwitchPlaylistKeyDown = isSwitchPlaylistDown;
            _wasSkipKeyDown = isSkipDown;
            _wasPreviousKeyDown = isPrevDown;
            _wasFastForwardKeyDown = isFfDown;
            _wasRewindKeyDown = isRwDown;
            _wasRepeatKeyDown = isRepeatDown;
            _wasShuffleKeyDown = isShuffleDown;

            if (!extVolInstalled)
            {
                string volUpStr = GetStringConfigValue(_volumeUpKeyEntry, "Add");
                if (volUpStr != _cachedVolUpStr)
                {
                    _cachedVolUpStr = volUpStr;
                    _cachedVolUpVKey = ResolveVirtualKey(_cachedVolUpStr);
                }
                string volDownStr = GetStringConfigValue(_volumeDownKeyEntry, "Subtract");
                if (volDownStr != _cachedVolDownStr)
                {
                    _cachedVolDownStr = volDownStr;
                    _cachedVolDownVKey = ResolveVirtualKey(_cachedVolDownStr);
                }

                bool isVolUpDown = (GetAsyncKeyState(_cachedVolUpVKey) & 0x8000) != 0;
                bool isVolDownDown = (GetAsyncKeyState(_cachedVolDownVKey) & 0x8000) != 0;

                if (isVolUpDown || isVolDownDown)
                {
                    float step = GetVolumeStepAmount();
                    bool justPressed = (isVolUpDown && !_wasVolUpKeyDown) || (isVolDownDown && !_wasVolDownKeyDown);
                    if (justPressed)
                    {
                        AdjustIntegratedVolume(isVolUpDown ? step : -step);
                        _volumeHoldTimer = VolumeInitialHoldDelay;
                    }
                    else
                    {
                        _volumeHoldTimer -= Time.unscaledDeltaTime;
                        if (_volumeHoldTimer <= 0f)
                        {
                            AdjustIntegratedVolume(isVolUpDown ? step : -step);
                            _volumeHoldTimer = VolumeRepeatInterval;
                        }
                    }
                }
                else
                {
                    _volumeHoldTimer = 0f;
                }
                _wasVolUpKeyDown = isVolUpDown;
                _wasVolDownKeyDown = isVolDownDown;
            }
            else
            {
                _wasVolUpKeyDown = false;
                _wasVolDownKeyDown = false;
                _volumeHoldTimer = 0f;
            }

            if (playPauseTriggered)
            {
                if (is2DMode) ToggleStandalone2DPlayPause();
                else Toggle3DPlayPause(nearestBoombox, nearestRadioPlayer);
            }
            if (switchPlaylistTriggered) SwitchToNextPlaylist(nearestBoombox, nearestRadioPlayer);
            if (skipTriggered) SkipNearestActiveRadio(nearestBoombox, nearestRadioPlayer);
            if (prevTriggered) PreviousNearestActiveRadio(nearestBoombox, nearestRadioPlayer);
            if (ffTriggered) SeekNearestActiveRadio(nearestBoombox, nearestRadioPlayer, 30000);
            if (rwTriggered) SeekNearestActiveRadio(nearestBoombox, nearestRadioPlayer, -15000);
            if (repeatTriggered)
            {
                _isRepeatSingleTrack = !_isRepeatSingleTrack;
                ShowHudMessage("Repeat Track", _isRepeatSingleTrack ? "ON" : "OFF");
            }
            if (shuffleTriggered)
            {
                _isShuffleEnabled = !_isShuffleEnabled;
                ShowHudMessage("Shuffle", _isShuffleEnabled ? "ON" : "OFF");
            }
        }

        private static void FindNearestActiveEvent(out Radio nearestBoombox, out RadioPlayer nearestRadioPlayer)
        {
            Vector3 playerPos = LocalPlayer.Transform.position;
            float maxRadius = GetMaxControlRadius();
            float bestDistSq = maxRadius * maxRadius;
            nearestBoombox = null;
            nearestRadioPlayer = null;
            for (int i = ActiveBoomboxes.Count - 1; i >= 0; i--)
            {
                Radio radio = ActiveBoomboxes[i];
                if (radio == null)
                {
                    ActiveBoomboxes.RemoveAt(i);
                    continue;
                }
                if (!radio._isOn || radio._isBroken) continue;
                float distSq = (playerPos - radio.transform.position).sqrMagnitude;
                if (distSq < bestDistSq)
                {
                    bestDistSq = distSq;
                    nearestBoombox = radio;
                    nearestRadioPlayer = null;
                }
            }
            for (int i = ActiveRadioPlayers.Count - 1; i >= 0; i--)
            {
                RadioPlayer rp = ActiveRadioPlayers[i];
                if (rp == null)
                {
                    ActiveRadioPlayers.RemoveAt(i);
                    continue;
                }
                if (!rp._isOn) continue;
                float distSq = (playerPos - rp.transform.position).sqrMagnitude;
                if (distSq < bestDistSq || (nearestBoombox == null && nearestRadioPlayer == null))
                {
                    bestDistSq = distSq;
                    nearestRadioPlayer = rp;
                    nearestBoombox = null;
                }
            }
        }
        private static void Toggle3DPlayPause(Radio nearestBoombox, RadioPlayer nearestRadioPlayer)
        {
            if (Mp3Files.Count == 0) return;
            EventInstance targetEvent = default(EventInstance);
            RadioRuntimeState targetState = null;
            if (nearestBoombox != null && nearestBoombox._playingEvent.isValid())
            {
                targetEvent = nearestBoombox._playingEvent;
                targetState = GetOrCreateState(nearestBoombox.GetInstanceID());
            }
            else if (nearestRadioPlayer != null && nearestRadioPlayer._playingEvent.isValid())
            {
                targetEvent = nearestRadioPlayer._playingEvent;
                targetState = GetOrCreateState(nearestRadioPlayer.GetInstanceID());
            }
            if (!targetEvent.isValid() || targetState == null) return;

            float now = Time.realtimeSinceStartup;
            PlaybackTimerState timerState;
            _instanceTimerStates.TryGetValue(targetEvent.handle, out timerState);
            string title = Path.GetFileNameWithoutExtension(Mp3Files[_lastPlayedTrackIndex % Mp3Files.Count]);

            if (!targetState.IsUserPaused)
            {
                targetState.IsUserPaused = true;
                targetEvent.setPaused(true);
                if (timerState != null && timerState.ChannelAnchored)
                {
                    float elapsedSec = Math.Max(0f, now - timerState.AnchorRealtime);
                    timerState.AnchorPositionMs += (uint)(elapsedSec * 1000f);
                    timerState.AnchorRealtime = now;
                }
                ShowHudMessage("Paused", title);
            }
            else
            {
                targetState.IsUserPaused = false;
                targetEvent.setPaused(false);
                if (timerState != null)
                {
                    timerState.AnchorRealtime = now;
                }
                ShowHudMessage("Resumed", title);
            }
        }
        private static void SwitchToNextPlaylist(Radio nearestBoombox, RadioPlayer nearestRadioPlayer)
        {
            if (_playlistNames.Count == 0) return;
            if (_playlistNames.Count == 1)
            {
                ShowHudMessage("Playlist", _playlistNames[0]);
                return;
            }

            ClearPlaybackBookmark();
            int nextIdx = (_currentPlaylistIndex + 1) % _playlistNames.Count;
            string nextName = _playlistNames[nextIdx];
            ApplyActivePlaylistSelection(nextName);
            if (Mp3Files.Count == 0)
            {
                ShowHudMessage("Playlist", $"{nextName} (0 tracks)");
                return;
            }

            if (IsBoombox2DEnabled())
            {
                ForceSkipRequested = true;
                SuppressNextHudPopup = true;
                StartStandalone2DTrack(showHud: false);
                SuppressNextHudPopup = false;
                ForceSkipRequested = false;
            }
            else if (nearestBoombox != null)
            {
                GetOrCreateState(nearestBoombox.GetInstanceID()).IsUserPaused = false;
                ForceSkipRequested = true;
                SuppressNextHudPopup = true;
                nearestBoombox.StartEvent("");
                SuppressNextHudPopup = false;
                ForceSkipRequested = false;
            }
            else if (nearestRadioPlayer != null)
            {
                GetOrCreateState(nearestRadioPlayer.GetInstanceID()).IsUserPaused = false;
                ForceSkipRequested = true;
                SuppressNextHudPopup = true;
                nearestRadioPlayer.StartEvent("");
                SuppressNextHudPopup = false;
                ForceSkipRequested = false;
            }

            string switchedTrackPath = Mp3Files[_lastPlayedTrackIndex % Mp3Files.Count];
            string trackTitle = Path.GetFileNameWithoutExtension(switchedTrackPath);
            ShowHudMessage(BuildTrackHudPrefix(switchedTrackPath, "Root"), trackTitle);
        }
        private static void SkipNearestActiveRadio(Radio nearestBoombox, RadioPlayer nearestRadioPlayer)
        {
            ClearPlaybackBookmark();
            if (IsBoombox2DEnabled())
            {
                ForceSkipRequested = true;
                StartStandalone2DTrack(showHud: true);
                ForceSkipRequested = false;
                return;
            }
            if (nearestBoombox != null)
            {
                GetOrCreateState(nearestBoombox.GetInstanceID()).IsUserPaused = false;
                ForceSkipRequested = true;
                nearestBoombox.StartEvent("");
                ForceSkipRequested = false;
            }
            else if (nearestRadioPlayer != null)
            {
                GetOrCreateState(nearestRadioPlayer.GetInstanceID()).IsUserPaused = false;
                ForceSkipRequested = true;
                nearestRadioPlayer.StartEvent("");
                ForceSkipRequested = false;
            }
        }
        private static void PreviousNearestActiveRadio(Radio nearestBoombox, RadioPlayer nearestRadioPlayer)
        {
            if (Mp3Files.Count == 0) return;
            if (!IsBoombox2DEnabled() && nearestBoombox == null && nearestRadioPlayer == null) return;
            int count = Mp3Files.Count;
            _currentTrackIndex = ((_currentTrackIndex - 2) % count + count) % count;
            SkipNearestActiveRadio(nearestBoombox, nearestRadioPlayer);
        }
        private static IntPtr FindActiveChannelInGroup(IntPtr groupPtr)
        {
            if (groupPtr == IntPtr.Zero) return IntPtr.Zero;
            int numChannels;
            if (FMOD_ChannelGroup_GetNumChannels(groupPtr, out numChannels) == RESULT.OK)
            {
                for (int i = 0; i < numChannels; i++)
                {
                    IntPtr chPtr;
                    if (FMOD_ChannelGroup_GetChannel(groupPtr, i, out chPtr) == RESULT.OK && chPtr != IntPtr.Zero)
                    {
                        int isPlaying;
                        FMOD_Channel_IsPlaying(chPtr, out isPlaying);
                        if (isPlaying != 0) return chPtr;
                    }
                }
            }
            int numGroups;
            if (FMOD_ChannelGroup_GetNumGroups(groupPtr, out numGroups) == RESULT.OK)
            {
                for (int i = 0; i < numGroups; i++)
                {
                    IntPtr subGroupPtr;
                    if (FMOD_ChannelGroup_GetGroup(groupPtr, i, out subGroupPtr) == RESULT.OK && subGroupPtr != IntPtr.Zero)
                    {
                        IntPtr found = FindActiveChannelInGroup(subGroupPtr);
                        if (found != IntPtr.Zero) return found;
                    }
                }
            }
            return IntPtr.Zero;
        }
        public static bool IsChannelRegistered(IntPtr instanceHandle)
        {
            return instanceHandle != IntPtr.Zero && _instanceToChannelMap.ContainsKey(instanceHandle);
        }
        public static void RegisterActiveChannelForInstance(IntPtr instanceHandle, RadioRuntimeState state, float now)
        {
            if (instanceHandle == IntPtr.Zero) return;
            if (_instanceToChannelMap.ContainsKey(instanceHandle)) return;
            if ((now - state.LastChannelLookupTime) < 0.15f) return;
            state.LastChannelLookupTime = now;
            IntPtr groupPtr;
            if (FMOD_Studio_EventInstance_GetChannelGroup(instanceHandle, out groupPtr) == RESULT.OK && groupPtr != IntPtr.Zero)
            {
                IntPtr activeChannel = FindActiveChannelInGroup(groupPtr);
                if (activeChannel != IntPtr.Zero)
                {
                    _instanceToChannelMap[instanceHandle] = activeChannel;
                    if (CoreSystem.handle != IntPtr.Zero && !_instanceToDspMap.ContainsKey(instanceHandle))
                    {
                        IntPtr limiterDsp;
                        RESULT createRes = FMOD_System_CreateDSPByType(CoreSystem.handle, FMOD_DSP_TYPE_LIMITER, out limiterDsp);
                        if (createRes == RESULT.OK && limiterDsp != IntPtr.Zero)
                        {
                            FMOD_DSP_SetParameterFloat(limiterDsp, 0, 40.0f); // Release time (40ms, prevents bass pumping)
                            FMOD_DSP_SetParameterFloat(limiterDsp, 1, 0.0f);  // Ceiling (0.0 dB, catches over-loud tracks safely)
                            if (FMOD_ChannelGroup_AddDSP(groupPtr, 0, limiterDsp) == RESULT.OK)
                            {
                                _instanceToDspMap[instanceHandle] = limiterDsp;
                            }
                            else
                            {
                                FMOD_DSP_Release(limiterDsp);
                            }
                        }
                    }
                    float volScale = (_standalone2DEvent.isValid() && instanceHandle == _standalone2DEvent.handle)
                        ? GetWalkman2DVolume()
                        : Mathf.Clamp(_current3DVolume, 0.0f, 1.5f);
                    FMOD_Channel_SetVolume(activeChannel, _currentFadeMultiplier * volScale * 0.60f);
                    PlaybackTimerState timerState;
                    if (_instanceTimerStates.TryGetValue(instanceHandle, out timerState) && !timerState.ChannelAnchored)
                    {
                        uint startPosMs = 0;
                        if (timerState.PendingStartSeekMs > 0)
                        {
                            uint targetSeekMs = timerState.PendingStartSeekMs;
                            timerState.PendingStartSeekMs = 0;
                            if (timerState.TotalLengthMs > 1000 && targetSeekMs >= timerState.TotalLengthMs - 500)
                            {
                                targetSeekMs = timerState.TotalLengthMs - 500;
                            }
                            if (FMOD_Channel_SetPosition(activeChannel, targetSeekMs, FMOD_TIMEUNIT_MS) == RESULT.OK)
                            {
                                startPosMs = targetSeekMs;
                            }
                        }
                        timerState.AnchorPositionMs = startPosMs;
                        timerState.AnchorRealtime = now;
                        timerState.ChannelAnchored = true;
                        if (_standalone2DEvent.isValid() && instanceHandle == _standalone2DEvent.handle && !_isStandalone2DPaused && timerState.TotalLengthMs > 0)
                        {
                            uint remMs = timerState.TotalLengthMs > startPosMs ? (timerState.TotalLengthMs - startPosMs) : 0;
                            _standalone2DEndTime = now + (remMs / 1000f) + 0.35f;
                        }
                    }
                }
            }
        }
        public static bool IsSilentStalledStream(EventInstance eventInstance, float now)
        {
            if (!eventInstance.isValid()) return false;
            IntPtr h = eventInstance.handle;
            if (_instanceToChannelMap.ContainsKey(h)) return false;
            float startTime;
            if (_instanceStartTimes.TryGetValue(h, out startTime))
            {
                if ((now - startTime) > 3.5f)
                {
                    return true;
                }
            }
            return false;
        }
        private static void SeekNearestActiveRadio(Radio nearestBoombox, RadioPlayer nearestRadioPlayer, int deltaMs)
        {
            EventInstance targetEvent = default(EventInstance);
            if (IsBoombox2DEnabled() && _standalone2DEvent.isValid())
            {
                targetEvent = _standalone2DEvent;
            }
            else if (nearestBoombox != null && nearestBoombox._playingEvent.isValid())
            {
                targetEvent = nearestBoombox._playingEvent;
            }
            else if (nearestRadioPlayer != null && nearestRadioPlayer._playingEvent.isValid())
            {
                targetEvent = nearestRadioPlayer._playingEvent;
            }
            if (!targetEvent.isValid()) return;
            IntPtr handle = targetEvent.handle;
            IntPtr activeChannel;
            if (!_instanceToChannelMap.TryGetValue(handle, out activeChannel) || activeChannel == IntPtr.Zero)
            {
                return;
            }
            uint totalLengthMs = 0;
            PlaybackTimerState timerState;
            IntPtr targetSoundHandle;
            if (_instanceTimerStates.TryGetValue(handle, out timerState))
            {
                totalLengthMs = timerState.TotalLengthMs;
            }
            else if (_activePlayingSounds.TryGetValue(handle, out targetSoundHandle) && targetSoundHandle != IntPtr.Zero)
            {
                FMOD_Sound_GetLength(targetSoundHandle, out totalLengthMs, FMOD_TIMEUNIT_MS);
            }
            float now = Time.realtimeSinceStartup;
            uint currentPosMs = 0;
            if (timerState != null && timerState.ChannelAnchored)
            {
                float elapsedSec = Math.Max(0f, now - timerState.AnchorRealtime);
                currentPosMs = timerState.AnchorPositionMs + (uint)(elapsedSec * 1000f);
            }
            else
            {
                FMOD_Channel_GetPosition(activeChannel, out currentPosMs, FMOD_TIMEUNIT_MS);
            }
            long targetMs = (long)currentPosMs + deltaMs;

            if (targetMs < 0)
            {
                targetMs = 0;
            }
            if (totalLengthMs > 1000 && targetMs >= totalLengthMs - 500)
            {
                targetMs = totalLengthMs - 500;
            }
            uint newPosMs = (uint)targetMs;
            RESULT seekRes = FMOD_Channel_SetPosition(activeChannel, newPosMs, FMOD_TIMEUNIT_MS);
            if (seekRes == RESULT.OK)
            {
                if (timerState != null)
                {
                    timerState.AnchorPositionMs = newPosMs;
                    timerState.AnchorRealtime = Time.realtimeSinceStartup;
                    timerState.ChannelAnchored = true;
                    if (_standalone2DEvent.isValid() && handle == _standalone2DEvent.handle && !_isStandalone2DPaused && timerState.TotalLengthMs > 0)
                    {
                        uint remMs = timerState.TotalLengthMs > newPosMs ? (timerState.TotalLengthMs - newPosMs) : 0;
                        _standalone2DEndTime = timerState.AnchorRealtime + (remMs / 1000f) + 0.35f;
                    }
                }
                string curFormatted = FormatTimeMs(newPosMs);
                string totalFormatted = FormatTimeMs(totalLengthMs);
                string label = deltaMs >= 0
                ? $"Fast Forward +{deltaMs / 1000}s"
                : $"Rewind {deltaMs / 1000}s";
                ShowHudMessage(label, $"{curFormatted} / {totalFormatted}");
            }
        }
        private static string FormatTimeMs(uint ms)
        {
            TimeSpan ts = TimeSpan.FromMilliseconds(ms);
            return ts.TotalHours >= 1.0
            ? $"{(int)ts.TotalHours}:{ts.Minutes:D2}:{ts.Seconds:D2}"
            : $"{ts.Minutes:D2}:{ts.Seconds:D2}";
        }
        public static void InitializeCustomBanks(FMOD.Studio.System studioSys)
        {
            if (IsFmodReady || studioSys.handle == IntPtr.Zero) return;
            StudioSystem = studioSys;
            StudioSystem.getCoreSystem(out CoreSystem);
            IsFmodReady = true;
            string bankPath = Path.Combine(_modFolder, "CustomRadio.bank");
            if (File.Exists(bankPath))
            {
                RESULT bankRes = StudioSystem.loadBankFile(bankPath, LOAD_BANK_FLAGS.NORMAL, out _customBank);
                if (bankRes == RESULT.OK)
                {
                    _customBank.loadSampleData();
                }
                RLog.Msg($"mp3player: CustomRadio.bank load result = {bankRes}");
            }
            else
            {
                RLog.Warning($"mp3player: Missing {bankPath}!");
            }
        }
        public static void ReleaseSoundForInstance(IntPtr instanceHandle)
        {
            if (instanceHandle == IntPtr.Zero) return;
            lock (_fmodNativeLock)
            {
                IntPtr channelPtr;
                float dummyFloat;
                PlaybackTimerState dummyTimer;
                _instanceToChannelMap.TryRemove(instanceHandle, out channelPtr);
                IntPtr limiterDsp;
                if (_instanceToDspMap.TryRemove(instanceHandle, out limiterDsp) && limiterDsp != IntPtr.Zero)
                {
                    IntPtr groupPtr;
                    if (FMOD_Studio_EventInstance_GetChannelGroup(instanceHandle, out groupPtr) == RESULT.OK && groupPtr != IntPtr.Zero)
                    {
                        FMOD_ChannelGroup_RemoveDSP(groupPtr, limiterDsp);
                    }
                    FMOD_DSP_Release(limiterDsp);
                }
                _instanceStartTimes.TryRemove(instanceHandle, out dummyFloat);
                _instanceTimerStates.TryRemove(instanceHandle, out dummyTimer);
                IntPtr pendingSound;
                if (_instanceToSoundMap.TryRemove(instanceHandle, out pendingSound) && pendingSound != IntPtr.Zero)
                {
                    var s = new Sound { handle = pendingSound };
                    s.release();
                }
                IntPtr activeSound;
                if (_activePlayingSounds.TryRemove(instanceHandle, out activeSound) && activeSound != IntPtr.Zero)
                {
                    var s = new Sound { handle = activeSound };
                    s.release();
                }
            }
        }
        public static bool IsCustomEventStillPlaying(EventInstance eventInstance)
        {
            if (ForceSkipRequested || !IsInsideRadioUpdate) return false;
            if (!eventInstance.isValid()) return false;
            IntPtr h = eventInstance.handle;
            if (!_activePlayingSounds.ContainsKey(h) && !_instanceToSoundMap.ContainsKey(h))
            {
                return false;
            }
            PLAYBACK_STATE state;
            eventInstance.getPlaybackState(out state);
            return state == PLAYBACK_STATE.PLAYING || state == PLAYBACK_STATE.STARTING;
        }
        public static bool HasTrackFinished(EventInstance eventInstance, float now)
        {
            if (!eventInstance.isValid()) return false;
            PLAYBACK_STATE state;
            eventInstance.getPlaybackState(out state);
            if (state == PLAYBACK_STATE.STOPPED)
            {
                return true;
            }
            IntPtr h = eventInstance.handle;
            float startTime;
            if (_instanceStartTimes.TryGetValue(h, out startTime) && (now - startTime) < 3.0f)
            {
                return false;
            }
            PlaybackTimerState timerState;
            if (_instanceTimerStates.TryGetValue(h, out timerState) && timerState.ChannelAnchored && timerState.TotalLengthMs > 0)
            {
                float elapsedSec = Math.Max(0f, now - timerState.AnchorRealtime);
                uint currentPosMs = timerState.AnchorPositionMs + (uint)(elapsedSec * 1000f);
                return currentPosMs >= (timerState.TotalLengthMs + 350);
            }
            if (_activePlayingSounds.ContainsKey(h))
            {
                IntPtr groupPtr;
                if (FMOD_Studio_EventInstance_GetChannelGroup(h, out groupPtr) == RESULT.OK && groupPtr != IntPtr.Zero)
                {
                    IntPtr activeChannel = FindActiveChannelInGroup(groupPtr);
                    if (activeChannel == IntPtr.Zero)
                    {
                        return true;
                    }
                }
            }
            return false;

        }
        public static ATTRIBUTES_3D Build3DAttributes(Transform speakerTransform)
        {
            Vector3 pos = speakerTransform.position;
            Vector3 forward = speakerTransform.forward;
            Vector3 up = speakerTransform.up;
            if (pos == Vector3.zero)
            {
                Camera cam = GetMainCamera();
                if (cam != null)
                {
                    pos = cam.transform.position;
                }
            }
            return new ATTRIBUTES_3D
            {
                position = new VECTOR { x = pos.x, y = pos.y, z = pos.z },
                velocity = new VECTOR { x = 0f, y = 0f, z = 0f },
                forward = new VECTOR { x = forward.x, y = forward.y, z = forward.z },
                up = new VECTOR { x = up.x, y = up.y, z = up.z }
            };
        }
        public static EventInstance CreateCustomStreamInstance(Transform speakerTransform, float volume, bool showHud = false, bool is2D = false)
        {
            float distSqToPlayer;
            if (!TryGetDistanceSqToPlayer(speakerTransform, out distSqToPlayer))
            {
                return default(EventInstance);
            }
            if (!is2D && distSqToPlayer > MaxAudibleDistanceSq)
            {
                return default(EventInstance);
            }
            EventDescription eventDesc;
             Il2CppSystem.Guid targetGuid = is2D ? CustomEvent2DGuid : CustomEventGuid;
             RESULT descRes = StudioSystem.getEventByID(targetGuid, out eventDesc);

            if (descRes != RESULT.OK || !eventDesc.isValid())
            {
                RLog.Warning($"mp3player: Failed to find event by GUID! Result = {descRes}");
                return default(EventInstance);
            }
            if (Mp3Files.Count == 0) return default(EventInstance);
            bool isAutoRepeating = KeepCurrentTrackOnRestart || (_isRepeatSingleTrack && IsNaturalAutoAdvance);
            uint pendingSeekForThisStream = 0;
            int playIdx;
            if (_resumeSavedPositionOnNextStart && _savedPositionMs > 0)
            {
                playIdx = _savedTrackIndex % Mp3Files.Count;
                pendingSeekForThisStream = _savedPositionMs;
                _resumeSavedPositionOnNextStart = false;
            }
            else if (isAutoRepeating)
            {
                playIdx = _lastPlayedTrackIndex % Mp3Files.Count;
            }
            else if (_isShuffleEnabled && Mp3Files.Count > 1)
            {
                int candidate = _rng.Next(Mp3Files.Count - 1);
                if (candidate >= (_lastPlayedTrackIndex % Mp3Files.Count))
                {
                    candidate++;
                }
                playIdx = candidate;
            }
            else
            {
                playIdx = _currentTrackIndex % Mp3Files.Count;
            }
            _lastPlayedTrackIndex = playIdx;
            if (!isAutoRepeating || (_currentTrackIndex % Mp3Files.Count) == playIdx)
            {
                _currentTrackIndex = (playIdx + 1) % Mp3Files.Count;
            }
            string trackPath = null;
            Sound preloadedSound = default(Sound);
            MODE soundMode = MODE.CREATESTREAM | MODE._2D;
            bool foundPlayable = false;
            int attempts = Mp3Files.Count;

            for (int attempt = 0; attempt < attempts; attempt++)
            {
                int candidateIdx = (playIdx + attempt) % Mp3Files.Count;
                string candidatePath = Mp3Files[candidateIdx];
                if (string.IsNullOrEmpty(candidatePath) || !File.Exists(candidatePath))
                {
                    RLog.Warning($"mp3player: Skipping missing track {Path.GetFileName(candidatePath ?? "unknown")}");
                    continue;
                }
                RESULT soundRes = CoreSystem.createSound(candidatePath, soundMode, out preloadedSound);
                if (soundRes == RESULT.OK && preloadedSound.handle != IntPtr.Zero)
                {
                    playIdx = candidateIdx;
                    trackPath = candidatePath;
                    _lastPlayedTrackIndex = playIdx;
                    if (!isAutoRepeating)
                    {
                        _currentTrackIndex = (playIdx + 1) % Mp3Files.Count;
                    }
                    foundPlayable = true;
                    break;
                }
                RLog.Warning($"mp3player: Failed to create stream for {Path.GetFileName(candidatePath)}! Result = {soundRes}");
            }

            if (!foundPlayable)
            {
                return default(EventInstance);
            }
            uint trackLengthMs;
            if (!_trackLengthMsCache.TryGetValue(trackPath, out trackLengthMs))
            {
                FMOD_Sound_GetLength(preloadedSound.handle, out trackLengthMs, FMOD_TIMEUNIT_MS);
                if (trackLengthMs > 0)
                {
                    _trackLengthMsCache[trackPath] = trackLengthMs;
                }
            }
            EventInstance instance;
            eventDesc.createInstance(out instance);
            if (!instance.isValid())
            {
                preloadedSound.release();
                return default(EventInstance);
            }
            float now = Time.realtimeSinceStartup;
            IntPtr instHandle = instance.handle;
            _instanceToSoundMap[instHandle] = preloadedSound.handle;
            _instanceTimerStates[instHandle] = new PlaybackTimerState
            {
                TotalLengthMs = trackLengthMs,
                AnchorPositionMs = pendingSeekForThisStream,
                AnchorRealtime = now,
                ChannelAnchored = false,
                PendingStartSeekMs = pendingSeekForThisStream
            };
            FMOD_Studio_EventInstance_SetCallback(
            instHandle,
            _nativeCallbackPtr,
            EVENT_CALLBACK_TYPE.CREATE_PROGRAMMER_SOUND
            );
            float effectiveVol = is2D
                ? Mathf.Clamp(volume, 0.0f, 1.5f)
                : Mathf.Clamp(volume * _current3DVolume, 0.0f, 1.5f);
            if (!is2D)
            {
                instance.set3DAttributes(Build3DAttributes(speakerTransform));
            }
            instance.setVolume(effectiveVol);
            instance.start();
            instance.setVolume(effectiveVol);
            _instanceStartTimes[instHandle] = now;
            bool isWorldSettled = IsPlayerInActiveWorld() && _worldReadyTime > 0f && (now - _worldReadyTime) > 2.5f;
            float maxRad = GetMaxControlRadius();
            if (!SuppressNextHudPopup && (ForceSkipRequested || (showHud && isWorldSettled)) && (is2D || distSqToPlayer <= (maxRad * maxRad)))
            {
                string title = Path.GetFileNameWithoutExtension(trackPath);
                ShowHudMessage(BuildTrackHudPrefix(trackPath, "Root"), title);
            }
            return instance;
        }
        private static RESULT ProgrammerSoundCallback(EVENT_CALLBACK_TYPE type, IntPtr eventInstance, IntPtr parameterPtr)
        {
            if (type == EVENT_CALLBACK_TYPE.CREATE_PROGRAMMER_SOUND && parameterPtr != IntPtr.Zero)
            {
                IntPtr soundHandle;
                if (_instanceToSoundMap.TryRemove(eventInstance, out soundHandle) && soundHandle != IntPtr.Zero)
                {
                    var props = (NativeProgrammerSoundProps)Marshal.PtrToStructure(parameterPtr, typeof(NativeProgrammerSoundProps));
                    props.sound = soundHandle;
                    props.subsoundIndex = -1;
                    Marshal.StructureToPtr(props, parameterPtr, false);
                    _activePlayingSounds[eventInstance] = soundHandle;
                }
            }
            return RESULT.OK;
        }
    }
    [HarmonyPatch(typeof(FMOD.Studio.System), nameof(FMOD.Studio.System.getEvent))]
    public static class FmodSystemCapturePatch
    {
        public static void Postfix(FMOD.Studio.System __instance)
        {
            if (!CustomRadioMod.IsFmodReady)
            {
                CustomRadioMod.InitializeCustomBanks(__instance);
            }
        }
    }
    [HarmonyPatch(typeof(RadioPlayer), nameof(RadioPlayer.StopEvent))]
    public static class RadioPlayerPreventPrematureStopPatch
    {
        public static bool Prefix(RadioPlayer __instance)
        {
            var st = CustomRadioMod.GetOrCreateState(__instance.GetInstanceID());
            EventInstance activeEvt = __instance._playingEvent.isValid() ? __instance._playingEvent : st.LastPlayingEvent;
            if (__instance._isOn && CustomRadioMod.IsInsideRadioUpdate && (CustomRadioMod.IsManagedCustomEvent(activeEvt) || CustomRadioMod.IsCustomEventStillPlaying(activeEvt)))
            {
                return false;
            }
            if (__instance._playingEvent.isValid())
            {
                CustomRadioMod.SavePlaybackBookmark(__instance._playingEvent, "BoomboxStopEvent");
                IntPtr handle = __instance._playingEvent.handle;
                __instance._playingEvent.stop(FMOD.Studio.STOP_MODE.IMMEDIATE);
                __instance._playingEvent.release();
                __instance._playingEvent = default(EventInstance);
                CustomRadioMod.ReleaseSoundForInstance(handle);
            }

            return true;
        }
    }

    [HarmonyPatch(typeof(RadioPlayer), "PlayNextSong")]
    public static class RadioPlayerPreventPrematureSkipPatch
    {
        public static bool Prefix(RadioPlayer __instance)
        {
            var st = CustomRadioMod.GetOrCreateState(__instance.GetInstanceID());
            EventInstance activeEvt = __instance._playingEvent.isValid() ? __instance._playingEvent : st.LastPlayingEvent;
            if (__instance._isOn && CustomRadioMod.IsInsideRadioUpdate && (CustomRadioMod.IsManagedCustomEvent(activeEvt) || CustomRadioMod.IsCustomEventStillPlaying(activeEvt)))
            {
                return false;
            }
            if (__instance._isOn && !CustomRadioMod.IsInsideRadioUpdate)
            {
                if (CustomRadioMod.IsManagedCustomEvent(activeEvt))
                {
                    CustomRadioMod.ClearPlaybackBookmark();
                    CustomRadioMod.ForceSkipRequested = true;
                }
                CustomRadioMod.IsCartStartingUp = true;
            }
            return true;
        }
        public static void Postfix()
        {
            if (!CustomRadioMod.IsInsideRadioUpdate)
            {
                CustomRadioMod.IsCartStartingUp = false;
                CustomRadioMod.ForceSkipRequested = false;
            }
        }
    }
    [HarmonyPatch(typeof(RadioPlayer), nameof(RadioPlayer.StartEvent))]
    public static class RadioPlayerStreamPatch
    {
        public static bool Prefix(RadioPlayer __instance)
        {
            var state = CustomRadioMod.GetOrCreateState(__instance.GetInstanceID());
            CustomRadioMod.RegisterRadioPlayer(__instance, state);
            if (CustomRadioMod.IsBoombox2DEnabled()) return false;
            if (!CustomRadioMod.IsFmodReady || CustomRadioMod.Mp3Files.Count == 0) return true;
            float distSq;
            if (!CustomRadioMod.TryGetDistanceSqToPlayer(__instance.transform, out distSq) || distSq > CustomRadioMod.MaxAudibleDistanceSq)
            {
                return false;
            }
            float now = Time.realtimeSinceStartup;
            bool allowImmediateStart = CustomRadioMod.ForceSkipRequested || CustomRadioMod.IsCartStartingUp;
            if (!allowImmediateStart && __instance._playingEvent.isValid() && CustomRadioMod.IsManagedCustomEvent(__instance._playingEvent))
            {
                if ((now - state.LastStartRequestTime) < 0.5f)
                {
                    return false;
                }
            }
            state.LastStartRequestTime = now;
            if (__instance._playingEvent.isValid())
            {
                IntPtr oldHandle = __instance._playingEvent.handle;
                __instance._playingEvent.stop(FMOD.Studio.STOP_MODE.IMMEDIATE);
                __instance._playingEvent.release();
                __instance._playingEvent = default(EventInstance);
                CustomRadioMod.ReleaseSoundForInstance(oldHandle);
            }
            for (int i = CustomRadioMod.ActiveBoomboxes.Count - 1; i >= 0; i--)
            {
                Radio r = CustomRadioMod.ActiveBoomboxes[i];
                if (r == null) continue;
                var bState = CustomRadioMod.GetOrCreateState(r.GetInstanceID());
                EventInstance bEvt = r._playingEvent.isValid() ? r._playingEvent : bState.LastPlayingEvent;
                if (r._isOn || bEvt.isValid())
                {
                    if (bEvt.isValid() && CustomRadioMod.IsManagedCustomEvent(bEvt))
                    {
                        CustomRadioMod.SavePlaybackBookmark(bEvt, "HandoffBoomboxToCart");
                        IntPtr bHandle = bEvt.handle;
                        bEvt.stop(FMOD.Studio.STOP_MODE.IMMEDIATE);
                        bEvt.release();
                        r._playingEvent = default(EventInstance);
                        CustomRadioMod.ReleaseSoundForInstance(bHandle);
                    }
                    r._isOn = false;
                    r._isEventPlaying = false;
                    bState.WasOn = false;
                    bState.LastPlayingEvent = default(EventInstance);
                }
            }
            if (!CustomRadioMod.ForceSkipRequested && CustomRadioMod._savedPositionMs > 0)
            {
                CustomRadioMod._resumeSavedPositionOnNextStart = true;
                CustomRadioMod.SuppressNextHudPopup = true;
            }
            var instance = CustomRadioMod.CreateCustomStreamInstance(__instance.transform, Math.Max(1.25f, __instance._volume), showHud: true, is2D: true);
            CustomRadioMod.SuppressNextHudPopup = false;
            if (!instance.isValid()) return false;
            state.LastPlayingEvent = instance;
            __instance._playingEvent = instance;
            __instance._isEventPlaying = true;
            __instance._isPlayingAdvert = false;
            __instance._eventLengthSec = 99999;
            return false;
        }
    }
    [HarmonyPatch(typeof(RadioPlayer), "Update")]
    public static class RadioPlayerPositionSyncPatch
    {
        public static void Prefix()
        {
            CustomRadioMod.IsInsideRadioUpdate = true;
        }
        public static void Postfix(RadioPlayer __instance)
        {
            CustomRadioMod.IsInsideRadioUpdate = false;
        }
    }
    [HarmonyPatch(typeof(Radio), nameof(Radio.StopEvent))]
    public static class BoomboxPreventPrematureStopPatch
    {
        public static bool Prefix(Radio __instance)
        {
            if (__instance._isOn && !__instance._isBroken && CustomRadioMod.IsCustomEventStillPlaying(__instance._playingEvent))
            {
                return false;
            }
            if (__instance._playingEvent.isValid())
            {
                IntPtr handle = __instance._playingEvent.handle;
                __instance._playingEvent.stop(FMOD.Studio.STOP_MODE.IMMEDIATE);
                __instance._playingEvent.release();
                __instance._playingEvent = default(EventInstance);
                CustomRadioMod.ReleaseSoundForInstance(handle);
            }

            return true;
        }
    }
    [HarmonyPatch(typeof(Radio), "PlayNextSong")]
    public static class BoomboxPreventPrematureSkipPatch
    {
        public static bool Prefix(Radio __instance)
        {
            if (__instance._isOn && !__instance._isBroken && CustomRadioMod.IsCustomEventStillPlaying(__instance._playingEvent))
            {
                return false;
            }
            return true;
        }
    }
    [HarmonyPatch(typeof(Radio), nameof(Radio.StartEvent))]
    public static class BoomboxStreamPatch
    {
        public static bool Prefix(Radio __instance)
        {
            var state = CustomRadioMod.GetOrCreateState(__instance.GetInstanceID());
            CustomRadioMod.RegisterBoombox(__instance, state);
            if (CustomRadioMod.IsBoombox2DEnabled()) return false;
            if (!CustomRadioMod.IsFmodReady || CustomRadioMod.Mp3Files.Count == 0) return true;
            float age = Time.realtimeSinceStartup - state.FirstSeenTime;
            if ((!__instance._isOn || __instance._isBroken || age < 0.35f || !state.WasOn) && !CustomRadioMod.ForceSkipRequested && !state.NeedsModeRestart)
            {
                return false;
            }
            state.NeedsModeRestart = false;
            float distSq;
            if (!CustomRadioMod.TryGetDistanceSqToPlayer(__instance.transform, out distSq) || distSq > CustomRadioMod.MaxAudibleDistanceSq)
            {
                return false;
            }
            float now = Time.realtimeSinceStartup;
            if (!CustomRadioMod.ForceSkipRequested && __instance._playingEvent.isValid() && CustomRadioMod.IsManagedCustomEvent(__instance._playingEvent))
            {
                if ((now - state.LastStartRequestTime) < 1.5f)
                {
                    return false;
                }
            }
            state.LastStartRequestTime = now;
            state.LastRestartTime = now;
            state.LastSyncTime = 0f;
            if (__instance._playingEvent.isValid())
            {
                IntPtr oldHandle = __instance._playingEvent.handle;
                __instance._playingEvent.stop(FMOD.Studio.STOP_MODE.IMMEDIATE);
                __instance._playingEvent.release();
                __instance._playingEvent = default(EventInstance);
                CustomRadioMod.ReleaseSoundForInstance(oldHandle);
            }
            var instance = CustomRadioMod.CreateCustomStreamInstance(__instance.transform, __instance._volume, showHud: true, is2D: false);
            if (!instance.isValid()) return false;
            __instance._playingEvent = instance;
            __instance._isEventPlaying = true;
            __instance._isPlayingAdvert = false;
            __instance._eventTimeSec = 0f;
            __instance._eventLengthSec = 99999;
            __instance._lastTrackStartTime = (int)now;
            return false;
        }
    }
    [HarmonyPatch(typeof(Radio), "Update")]
    public static class BoomboxPositionSyncPatch
    {
        public static void Prefix()
        {
            CustomRadioMod.IsInsideRadioUpdate = true;
        }
        public static void Postfix(Radio __instance)
        {
            CustomRadioMod.IsInsideRadioUpdate = false;
            if (!__instance._isOn || __instance._isBroken)
            {
                RadioRuntimeState offState;
                if (CustomRadioMod.TryGetState(__instance.GetInstanceID(), out offState) && offState != null)
                {
                    if (offState.WasOn && __instance._playingEvent.isValid())
                    {
                        if (!CustomRadioMod.IsBoombox2DEnabled() && CustomRadioMod.IsManagedCustomEvent(__instance._playingEvent))
                        {
                            CustomRadioMod.SavePlaybackBookmark(__instance._playingEvent, "BoomboxOffOrPickup");
                        }
                        IntPtr stopHandle = __instance._playingEvent.handle;
                        __instance._playingEvent.stop(FMOD.Studio.STOP_MODE.IMMEDIATE);
                        __instance._playingEvent.release();
                        __instance._playingEvent = default(EventInstance);
                        CustomRadioMod.ReleaseSoundForInstance(stopHandle);
                    }
                    offState.WasOn = false;
                    offState.IsUserPaused = false;
                    offState.CachedInRange = false;
                    CustomRadioMod.UpdateBoomboxLcd(__instance, offState, default(EventInstance), isActive: false);
                }
                return;
            }
            var state = CustomRadioMod.GetOrCreateState(__instance.GetInstanceID());
            float now = Time.realtimeSinceStartup;
            if (!state.WasOn)
            {
                state.WasOn = true;
                if (!CustomRadioMod.IsBoombox2DEnabled())
                {
                    for (int i = CustomRadioMod.ActiveRadioPlayers.Count - 1; i >= 0; i--)
                    {
                        RadioPlayer rp = CustomRadioMod.ActiveRadioPlayers[i];
                        if (rp == null) continue;
                        if (rp._isOn)
                        {
                            if (rp._playingEvent.isValid() && CustomRadioMod.IsManagedCustomEvent(rp._playingEvent))
                            {
                                CustomRadioMod.SavePlaybackBookmark(rp._playingEvent, "HandoffCartToBoombox");
                                IntPtr cHandle = rp._playingEvent.handle;
                                rp._playingEvent.stop(FMOD.Studio.STOP_MODE.IMMEDIATE);
                                rp._playingEvent.release();
                                rp._playingEvent = default(EventInstance);
                                CustomRadioMod.ReleaseSoundForInstance(cHandle);
                            }
                            rp._isOn = false;
                            rp._isEventPlaying = false;
                            var cState = CustomRadioMod.GetOrCreateState(rp.GetInstanceID());
                            cState.WasOn = false;
                        }
                    }
                    if (!CustomRadioMod.IsManagedCustomEvent(__instance._playingEvent))
                    {
                        if (_savedPositionMs > 0)
                        {
                            _resumeSavedPositionOnNextStart = true;
                            CustomRadioMod.SuppressNextHudPopup = true;
                        }
                        state.NeedsModeRestart = true;
                    }
                }
            }
            if ((now - state.LastRangeCheckTime) >= 0.25f)
            {
                state.LastRangeCheckTime = now;
                if (!state.IsRegistered)
                {
                    CustomRadioMod.RegisterBoombox(__instance, state);
                }
                float distSq;
                bool validPos = CustomRadioMod.TryGetDistanceSqToPlayer(__instance.transform, out distSq);
                state.CachedInRange = validPos && !CustomRadioMod.IsBoombox2DEnabled() && distSq <= CustomRadioMod.MaxAudibleDistanceSq;
            }
            if (!state.CachedInRange)
            {
                if (__instance._playingEvent.isValid())
                {
                    IntPtr stopHandle = __instance._playingEvent.handle;
                    __instance._playingEvent.stop(FMOD.Studio.STOP_MODE.IMMEDIATE);
                    __instance._playingEvent.release();
                    __instance._playingEvent = default(EventInstance);
                    CustomRadioMod.ReleaseSoundForInstance(stopHandle);
                }
                CustomRadioMod.UpdateBoomboxLcd(__instance, state, default(EventInstance), isActive: false);
                return;
            }
            if (CustomRadioMod.IsFmodReady && CustomRadioMod.Mp3Files.Count > 0 && !CustomRadioMod.IsManagedCustomEvent(__instance._playingEvent))
            {
                bool readyForFallbackRestart = (now - state.FirstSeenTime) >= 0.25f && __instance._isEventPlaying && __instance._playingEvent.isValid() && (now - state.LastRestartTime) > 2.0f;
                if (state.NeedsModeRestart || readyForFallbackRestart)
                {
                    state.NeedsModeRestart = false;
                    state.LastRestartTime = now;
                    CustomRadioMod.ForceSkipRequested = true;
                    CustomRadioMod.KeepCurrentTrackOnRestart = true;
                    CustomRadioMod.SuppressNextHudPopup = true;
                    __instance.StartEvent("");
                    CustomRadioMod.SuppressNextHudPopup = false;
                    CustomRadioMod.KeepCurrentTrackOnRestart = false;
                    CustomRadioMod.ForceSkipRequested = false;
                    return;
                }
            }
            if (__instance._playingEvent.isValid())
            {
                bool wasChannelBound = CustomRadioMod.IsChannelRegistered(__instance._playingEvent.handle);
                CustomRadioMod.RegisterActiveChannelForInstance(__instance._playingEvent.handle, state, now);
                bool isChannelBoundNow = CustomRadioMod.IsChannelRegistered(__instance._playingEvent.handle);
                if (!wasChannelBound && isChannelBoundNow)
                {
                    state.LastSyncTime = 0f;
                }
                CustomRadioMod.UpdateBoomboxLcd(__instance, state, __instance._playingEvent, isActive: true);
                if (!CustomRadioMod.IsBoombox2DEnabled() && isChannelBoundNow && (state.LastSyncTime <= 0f || (now - state.LastSyncTime) >= 0.25f))
                {
                    state.LastSyncTime = now;
                    __instance._playingEvent.set3DAttributes(CustomRadioMod.Build3DAttributes(__instance.transform));
                }
                __instance._eventTimeSec = 0f;
                __instance._eventLengthSec = 99999;
                if (_savedPositionMs > 0 && isChannelBoundNow && (now - state.LastStartRequestTime) > 1.5f)
                {
                    _savedPositionMs = 0;
                }
                if (!state.IsUserPaused && (now - state.LastFinishCheckTime) >= 0.50f)
                {
                    state.LastFinishCheckTime = now;
                    if (CustomRadioMod.HasTrackFinished(__instance._playingEvent, now) || CustomRadioMod.IsSilentStalledStream(__instance._playingEvent, now))
                    {
                        if ((now - state.LastRestartTime) > 3.5f)
                        {
                            state.LastRestartTime = now;
                            CustomRadioMod.ForceSkipRequested = true;
                            CustomRadioMod.IsNaturalAutoAdvance = true;
                            __instance.StartEvent("");
                            CustomRadioMod.IsNaturalAutoAdvance = false;
                            CustomRadioMod.ForceSkipRequested = false;
                        }
                    }
                }
            }
        }
    }
}