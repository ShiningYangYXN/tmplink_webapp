/**
 * VXUI Sync Drive Module
 * P2P file synchronization using WebRTC DataChannel + SQLite WASM
 * @version 1.0.0
 */

var VX_SYNC = VX_SYNC || {
    // ========== Configuration ==========
    _resolveSyncServer() {
        this.SYNC_API_URL = 'https://sync.5t-cdn.com:8981/api/sync';
        this.SYNC_SERVER_HOST = 'sync.5t-cdn.com';
        this.SYNC_SERVER_PORT = '8981';
        console.log('[SYNC] Server resolved: API=' + this.SYNC_API_URL + ' Host=' + this.SYNC_SERVER_HOST + ':' + this.SYNC_SERVER_PORT);
    },
    SYNC_API_URL: '',
    SYNC_SERVER_HOST: '',
    SYNC_SERVER_PORT: '',
    CHUNK_SIZE: 256 * 1024, // 256KB chunks (SCTP max-message-size default)
    
    // ========== State Management ==========
    currentDrive: null,       // {drive_id, drive_key, name, isHost}
    isHost: false,           // Whether this peer is the host
    drives: [],               // List of joined drives from backend
    serverAddr: null,        // Dynamic server address from API response (Phase 8)
    
    // WebRTC (P2P)
    rtcPeerConnection: null, // RTCPeerConnection instance (Peer side: single PC to Host)
    dataChannel: null,       // DataChannel (created by Host — legacy, kept for compat)
    acceptDC: null,          // DataChannel (accepted by Peer)
    _peerConnections: {},    // Host: peerDeviceId -> {pc, dc, mode, iceState, persistentId, displayName}
    _hostConnectionMode: 'unknown', // Peer: connection mode to Host ('p2p'|'wss_relay'|'unknown')
    
    // WebSocket signaling (single unified WSS connection, per-user)
    signalingWS: null,       // Unified WebSocket connection to sync_server (/ws)
    
    // File cache (in-memory only, populated from bound folder or P2P)
    fileCache: new Map(),    // sha1 -> {name, size, mtime, status, is_dir, parent_path}
    currentPath: '/',        // Current browsing path within drive
    
    // Transfer state
    pendingConflict: null,   // Current conflict being resolved
    _downloads: new Map(),   // sha1 → {chunks, meta, chunkSize, dc} for concurrent per-peer downloads
    peers: [],               // Online peers in current drive
    _reconnectTimer: null,   // Reconnect timer
    _reconnectAttempt: 0,    // Reconnect attempt count
    _reconnectMax: 10,       // Max reconnect attempts
    _peerCons: {},           // uid -> {pc: RTCPeerConnection, dc: DataChannel}
    _stunServersCache: null,  // {iceServers, expires} cached STUN server list
    _eligiblePeers: [],      // UIDs of eligible peers (latency < 100ms)
    _syncStatus: 'idle',     // 'idle' | 'ready' | 'syncing' | 'offline'
    _detailTab: 'files',     // 'files' | 'permissions' | 'peers' | 'activity' - active tab in detail view
    _mainTab: 'drives',       // 'drives' | 'messages' - active main tab
    _inviteCodes: [],         // Current invite codes for the drive
    _joinRequests: [],        // Current join requests for the drive
    _myPendingRequests: [],   // Applicant's own join requests (pending/approved/rejected) for card display
    _notifications: [],       // User's notifications
    _unreadNotificationCount: 0, // Count of unread notifications
    _currentDrivePermission: null, // 'read' or 'read_write' for shared drive users
    _ctxTarget: null,        // {sha1, name} for context menu target
    _hostOnline: true,       // Whether the drive host is online
    _boundFolder: null,      // {name, handle} for bound folder
    _activities: [],         // Activity log: [{type, desc, time, details}]
    _handleDb: null,         // IndexedDB connection for folder handle persistence
    _restorePromise: null,   // Promise for folder handle restoration
    _connectionMode: 'p2p',  // 'p2p' | 'wss_relay' | 'connecting' - current transport mode
    _relaySeq: 0,            // Monotonically increasing relay sequence number
    _relayReceivedSeq: null, // Set of received relay seqs for dedup
    _transferStats: {        // Transfer statistics
        filesUploaded: 0,
        filesDownloaded: 0,
        bytesUploaded: 0,
        bytesDownloaded: 0
    },
    _syncTimer: null,        // Periodic sync timer (bidirectional re-scan)
    _syncInterval: 3000,     // Current scan interval in ms (dynamically adjusted)
    _syncMinInterval: 3000,  // Minimum scan interval: 3 seconds
    _syncMaxInterval: 60000, // Maximum scan interval: 60 seconds
    _syncNoChangeCount: 0,   // Consecutive scans with no changes detected
    _immediateSyncTimer: null, // Debounce timer for immediate sync after file_op
    _fsObserver: null,          // FileSystemObserver instance (Chrome 129+), null if unsupported/inactive
    _fsObserverSupported: ('FileSystemObserver' in window), // Native file-change events available
    _peerReportDebounce: null,  // Debounce timer for peer re-report after receiving host push
    _lastScanFingerprints: null, // Map of path->fingerprint from last scan
    _loadingCount: 0,        // Counter for nested loading states
    deviceName: '',           // Current device display name (e.g., "#1" or custom name)
    _deviceNameLoaded: false, // Whether device name has been loaded from server
    _drivesLoadSucceeded: false, // Whether drive list was loaded successfully (for retry on reconnect)
    _transferQueue: [],      // Queue of pending file transfers (sha1 strings)
    _transferBusy: false,    // Whether a transfer is currently in progress
    _pendingDownloads: null, // Set of sha1s requested but not yet saved (prevents stale peer_file_report)
    _syncedFiles: {},        // Track synced file states: path -> { size, mtime, fingerprint }
    _syncInProgress: false,  // Prevent overlapping sync cycles
    _scanInProgress: false,  // Prevent overlapping periodic scans
    _drivesLoaded: false,    // Whether drive list has been loaded from server
    _peerLastPaths: null,    // Set of file paths Peer had last sync (null = first sync)
    _hostLastPaths: null,    // Set of file paths Host had last sync (null = first sync)
    _hostPendingOps: null,   // Pending Host operations: { path: { op: 'delete'|'rename'|'move', ts, newPath? } }
    _transferSpeed: 0,       // Current transfer speed in bytes/sec
    _transferStartTime: 0,   // Timestamp when current transfer started
    _transferLastBytes: 0,   // Bytes received/sent at last speed check
    _transferLastTime: 0,    // Timestamp of last speed check
    _transferSourceNode: '', // Display name of the node providing/receiving the file

    // ========== Multi-Session State ==========
    _tabID: '',                       // 当前 tab 的唯一标识（sessionStorage 持久，刷新同一 tab 保持不变）
    _bcastChannel: null,              // BroadcastChannel 实例（同浏览器多 tab 协调）
    _localDriveLocks: {},             // 本 tab 已知占用：drive_id -> { tab_id, role, folder_name }
    _lockFileHeartbeatTimer: null,    // 锁文件心跳定时器（1s 间隔，运行状态指示）
    sessions: new Map(),              // drive_id -> DriveSession（正在运行的同步盘实例）
    activeSessionId: null,            // 当前 UI 展示的 session drive_id

    /**
     * WebRTC Connection State Machine
     *
     * States:
     *   'disconnected'  – No active connection. Starting point.
     *   'connecting'    – initWebRTC() called, signaling WS connecting.
     *   'signaling'     – Signaling WS connected, offer/answer exchange in progress.
     *   'connected'     – DataChannel established, P2P sync active.
     *   'failed'        – Connection attempt failed, will reconnect.
     *
     * Rules:
     *   1. Only one transition at a time (prevents race conditions).
     *   2. All signaling messages are ignored if state doesn't match.
     *   3. Full state reset on every reconnect (_cleanupConnection).
     *   4. Host: only one offer in flight (_offerPending flag).
     *   5. Peer: only retry join when not in the middle of exchange.
     */
    _connState: 'disconnected',
    _fileStatus: new Map(),   // sha1 -> 'synced'|'pending_upload'|'remote_only'|'uploading'|'downloading'|'deleting'|'conflict'
    _fileProgress: new Map(), // sha1 -> percent (0-100)
    _currentTransferSha1: null, // sha1 of file currently being transferred
    _localFiles: [],          // Peer: local bound-folder files at currentPath [{name,size,mtime,is_dir,parent_path,sha1}]

    // ========== DriveSession ==========
    // 创建一个独立的 DriveSession 状态对象。
    // 所有原 this.xxx 单 drive 字段迁移到 session 内，实现多盘并行。
    _createDriveSession(drive, role) {
        return {
            drive_id: drive.drive_id,
            drive: drive,
            role: role,            // 'host' | 'peer'
            isHost: role === 'host',
            permission: null,      // 'read' | 'read_write'
            hostOnline: false,

            // 文件夹绑定
            boundFolder: null,     // { name, handle }
            lockNonce: null,       // 锁文件 nonce（持有锁的凭证）

            // 文件状态
            fileCache: new Map(),
            localFiles: [],
            fileStatus: new Map(),
            fileProgress: new Map(),
            currentPath: '/',

            // WebRTC (Peer 端)
            rtcPeerConnection: null,
            dataChannel: null,
            acceptDC: null,
            hostConnectionMode: 'unknown',

            // WebRTC (Host 端)
            peerConnections: {},   // peerId -> {pc, dc, mode, iceState, persistentId, displayName}
            peerDeviceIds: {},     // uid -> peerId

            // 传输
            downloads: new Map(),
            pendingDownloads: null,
            pendingDownloadTimeout: null,
            transferQueue: [],
            transferBusy: false,
            currentTransferSha1: null,
            transferStats: { filesUploaded: 0, filesDownloaded: 0, bytesUploaded: 0, bytesDownloaded: 0 },

            // 同步状态
            peerLastPaths: null,
            hostLastPaths: null,
            hostPendingOps: null,
            syncTimer: null,
            syncInProgress: false,
            scanInProgress: false,
            lastScanFingerprints: null,

            // 连接状态
            connState: 'disconnected',
            reconnectTimer: null,
            reconnectAttempt: 0,
            iceTimeout: null,
            connectTimeout: null,
            offerInProgress: false,
            offerTimeout: null,
            pendingSignaling: null,
            connectionMode: 'wss_relay',
            relaySeq: 0,
            relayReceivedSeq: null,
            syncStatus: 'idle',

            // FS 观察
            fsObserver: null,

            // 活动
            activities: [],

            // UI
            detailTab: 'files',
            peers: []
        };
    },

    // 获取当前活跃 session
    _getActiveSession() {
        if (!this.activeSessionId) return null;
        return this.sessions.get(this.activeSessionId) || null;
    },

    // 兼容访问器策略说明：
    // 旧代码大量使用 this.currentDrive / this.isHost / this._boundFolder 等。
    // 保留这些字段作为"当前活跃 session 的镜像"，在 switchSession 时同步更新。
    // 写入时双写（session + this），读取时统一从 this 读取。

    createSession(drive, role) {
        var session = this._createDriveSession(drive, role);
        this.sessions.set(drive.drive_id, session);
        return session;
    },

    destroySession(driveId) {
        var session = this.sessions.get(driveId);
        if (!session) return;
        this._cleanupSessionConnection(session);
        // 释放文件夹锁文件（异步，不阻塞）
        var self = this;
        this._releaseFolderLock(session).then(function() {});
        this._bcast('drive_unlocked', { drive_id: driveId });
        this.sessions.delete(driveId);
        if (this.activeSessionId === driveId) {
            this.activeSessionId = null;
            if (this.sessions.size > 0) {
                this.switchSession(this.sessions.keys().next().value);
            } else {
                this._showDriveList();
            }
        }
    },

    switchSession(driveId) {
        var session = this.sessions.get(driveId);
        if (!session) {
            console.warn('[SYNC] switchSession: session not found ' + driveId);
            return;
        }
        this.activeSessionId = driveId;
        // 同步镜像字段（所有旧代码 this.xxx 访问的来源）
        this.currentDrive = session.drive;
        this.isHost = session.isHost;
        this._boundFolder = session.boundFolder;
        this._hostOnline = session.hostOnline;
        this._currentDrivePermission = session.permission;
        this.fileCache = session.fileCache;
        this._localFiles = session.localFiles;
        this._fileStatus = session.fileStatus;
        this._fileProgress = session.fileProgress;
        this.currentPath = session.currentPath;
        this.peers = session.peers;
        this.rtcPeerConnection = session.rtcPeerConnection;
        this._peerConnections = session.peerConnections;
        this._peerDeviceIds = session.peerDeviceIds;
        this.dataChannel = session.dataChannel;
        this.acceptDC = session.acceptDC;
        this._hostConnectionMode = session.hostConnectionMode;
        this._downloads = session.downloads;
        this._pendingDownloads = session.pendingDownloads;
        this._transferQueue = session.transferQueue;
        this._transferBusy = session.transferBusy;
        this._currentTransferSha1 = session.currentTransferSha1;
        this._transferStats = session.transferStats;
        this._peerLastPaths = session.peerLastPaths;
        this._hostLastPaths = session.hostLastPaths;
        this._hostPendingOps = session.hostPendingOps;
        this._syncTimer = session.syncTimer;
        this._syncInProgress = session.syncInProgress;
        this._scanInProgress = session.scanInProgress;
        this._lastScanFingerprints = session.lastScanFingerprints;
        this._connState = session.connState;
        this._reconnectTimer = session.reconnectTimer;
        this._reconnectAttempt = session.reconnectAttempt;
        this._iceTimeout = session.iceTimeout;
        this._connectTimeout = session.connectTimeout;
        this._offerInProgress = session.offerInProgress;
        this._offerTimeout = session.offerTimeout;
        this._pendingSignaling = session.pendingSignaling;
        this._connectionMode = session.connectionMode;
        this._relaySeq = session.relaySeq;
        this._relayReceivedSeq = session.relayReceivedSeq;
        this._syncStatus = session.syncStatus;
        this._fsObserver = session.fsObserver;
        this._activities = session.activities;
        this._detailTab = session.detailTab;

        // 渲染 UI
        this._renderSessionSwitcher();
        this._renderActiveSession();
    },

    // 渲染顶部的 session 切换器（tab 条）
    _renderSessionSwitcher() {
        var container = document.getElementById('sync-session-tabs');
        if (!container) return;
        var self = this;
        container.innerHTML = '';
        this.sessions.forEach(function(session, driveId) {
            var tab = document.createElement('div');
            tab.className = 'vx-sync-session-tab' + (driveId === self.activeSessionId ? ' active' : '');
            var name = (session.drive && (session.drive.name || session.drive.drive_name)) || '同步盘';
            var roleTag = session.isHost ? 'H' : 'P';
            tab.innerHTML = '<span class="vx-sync-session-name">' + self.escapeHtml(name) + '</span>' +
                            '<span class="vx-sync-session-role">' + roleTag + '</span>' +
                            '<button class="vx-sync-session-close" title="关闭">&times;</button>';
            tab.onclick = function(e) {
                if (e.target.classList.contains('vx-sync-session-close')) {
                    e.stopPropagation();
                    self.leaveDrive(driveId);
                } else {
                    self.switchSession(driveId);
                }
            };
            container.appendChild(tab);
        });
        container.style.display = this.sessions.size > 1 ? 'flex' : 'none';
    },

    _showDriveList() {
        this.activeSessionId = null;
        this.currentDrive = null;
        this._renderSessionSwitcher();
        var list = document.getElementById('sync-drive-list');
        var detail = document.getElementById('sync-drive-detail');
        var lobby = document.getElementById('sync-drive-lobby');
        if (list) list.style.display = '';
        if (detail) detail.style.display = 'none';
        if (lobby) lobby.style.display = 'none';
    },

    _renderActiveSession() {
        var session = this._getActiveSession();
        if (!session) {
            this._showDriveList();
            return;
        }
        if (session.connState === 'disconnected' && !session.boundFolder) {
            this.showLobby();
        } else {
            // detail 视图渲染（复用现有 render 逻辑）
            var list = document.getElementById('sync-drive-list');
            var lobby = document.getElementById('sync-drive-lobby');
            var detail = document.getElementById('sync-drive-detail');
            if (list) list.style.display = 'none';
            if (lobby) lobby.style.display = 'none';
            if (detail) detail.style.display = '';
            this.render();
            this.renderActivityList();
        }
    },

    // ========== Initialization ==========
    init(params) {
        console.log('[SYNC] Initializing VX_SYNC module, token=' + (TL.api_token ? 'present' : 'absent') + ' uid=' + (TL.uid || 'unknown'));
        // Consent gate: must agree before first use. Stored in localStorage so
        // the user only needs to agree once per browser.
        if (!this._hasConsent()) {
            console.log('[SYNC] Consent not granted yet, showing consent modal');
            VXUI.openModal('sync-consent-modal');
            return;
        }

        // 生成或恢复 tab_id（sessionStorage 持久，刷新同一 tab 保持不变）
        try {
            this._tabID = sessionStorage.getItem('vx_sync_tab_id');
            if (!this._tabID) {
                this._tabID = 'tab_' + Date.now().toString(36) + '_' + Math.random().toString(36).substring(2, 8);
                sessionStorage.setItem('vx_sync_tab_id', this._tabID);
            }
        } catch (e) {
            this._tabID = 'tab_' + Date.now().toString(36);
        }

        // BroadcastChannel：同浏览器多 tab 协调
        try {
            this._bcastChannel = new BroadcastChannel('vx_sync');
            var self = this;
            this._bcastChannel.onmessage = function(ev) {
                self._handleBroadcastMessage(ev.data);
            };
        } catch (e) {
            console.warn('[SYNC] BroadcastChannel unavailable:', e);
        }

        this._resolveSyncServer();
        this._ensureDeviceId();
        this.setupDragDrop();
        // Connect single unified WSS channel — handles all drives and message types.
        this._connectWSS();
        // Now safe to load drives and device name (will wait for WSS to open).
        this.loadDrives();
        this._loadDeviceName();
        // Restore usage guide collapse state
        this._restoreGuideState();

        // 锁文件心跳：每 1s 更新所有 session 的 drive.lock heartbeat（运行状态指示）
        var self2 = this;
        this._lockFileHeartbeatTimer = setInterval(function() {
            self2._heartbeatLockFiles();
        }, 1000);

        // 页面卸载拦截：有活跃 session 时提示用户
        var selfUnload = this;
        window.addEventListener('beforeunload', function(e) {
            if (selfUnload.sessions.size > 0) {
                e.preventDefault();
                e.returnValue = selfUnload._t('sync_leave_warning');
                return e.returnValue;
            }
        });

        // pagehide: best-effort 释放（锁文件依赖 3s 过期回收）
        window.addEventListener('pagehide', function() {
            selfUnload._releaseAllLocksOnUnload();
        });
    },

    // Check whether the user has accepted the sync beta consent.
    _hasConsent() {
        try {
            return localStorage.getItem('vx_sync_consent_accepted') === '1';
        } catch (e) {
            return false;
        }
    },

    // ========== BroadcastChannel Coordination ==========

    // 向其它 tab 广播消息
    _bcast(type, data) {
        if (!this._bcastChannel) return;
        try {
            this._bcastChannel.postMessage(Object.assign({ type: type, tab_id: this._tabID }, data || {}));
        } catch (e) {}
    },

    // 处理来自其它 tab 的消息
    _handleBroadcastMessage(msg) {
        if (!msg || msg.tab_id === this._tabID) return;
        console.log('[SYNC] Broadcast from tab ' + msg.tab_id + ': ' + msg.type);
        switch (msg.type) {
            case 'drive_locked':
                this._localDriveLocks[msg.drive_id] = {
                    tab_id: msg.tab_id,
                    role: msg.role,
                    folder_name: msg.folder_name
                };
                // 更新 drive 卡片显示"已在其它 tab 打开"
                this.renderDriveList();
                break;
            case 'drive_unlocked':
                delete this._localDriveLocks[msg.drive_id];
                this.renderDriveList();
                break;
            case 'tab_unloading':
                // 其它 tab 正在卸载，清理它声明的占用（锁文件靠 3s 过期自动回收，这里仅清本地缓存）
                var toRemove = [];
                for (var did in this._localDriveLocks) {
                    if (this._localDriveLocks[did].tab_id === msg.tab_id) {
                        toRemove.push(did);
                    }
                }
                var changed = toRemove.length > 0;
                var self = this;
                toRemove.forEach(function(did) { delete self._localDriveLocks[did]; });
                if (changed) this.renderDriveList();
                break;
        }
    },

    // 锁文件心跳：每 1s 更新所有 session 的 drive.lock
    _heartbeatLockFiles() {
        if (!this.sessions || this.sessions.size === 0) return;
        var self = this;
        this.sessions.forEach(function(session) {
            self._touchDriveLockFile(session);
        });
    },

    // 页面卸载时的 best-effort 释放（锁文件依赖 3s 过期回收）
    _releaseAllLocksOnUnload() {
        if (this.sessions.size === 0) return;
        // 1. 广播给其它 tab
        this._bcast('tab_unloading', { tab_id: this._tabID });
        // 2. best-effort WSS drive_leave for each session
        if (this.signalingWS && this.signalingWS.readyState === WebSocket.OPEN) {
            var self = this;
            this.sessions.forEach(function(session) {
                try {
                    self.wsRequest('drive_leave', { drive_id: session.drive_id }, true);
                } catch (e) {}
            });
        }
        // 3. 锁文件无法在 pagehide 中可靠删除（File System Access API 是异步的），
        //    依赖 3s heartbeat 过期机制快速回收。
    },

    // User accepted the consent — persist and finish initializing the module.
    acceptConsent() {
        this.trackUI('sync_consent_accept');
        try {
            localStorage.setItem('vx_sync_consent_accepted', '1');
        } catch (e) {
            console.warn('[SYNC] Failed to persist consent flag:', e);
        }
        VXUI.closeModal('sync-consent-modal');
        console.log('[SYNC] Consent accepted, initializing module');
        this._resolveSyncServer();
        this._ensureDeviceId();
        this.setupDragDrop();
        this.loadDrives();
        this._connectWSS();
        this._loadDeviceName();
        this._restoreGuideState();
    },

    // User declined the consent — close modal and return to filelist module.
    declineConsent() {
        VXUI.closeModal('sync-consent-modal');
        if (typeof VXUI !== 'undefined' && typeof VXUI.navigate === 'function') {
            VXUI.navigate('filelist');
        }
    },

    // Generate or retrieve a persistent device ID from localStorage.
    // This identifies the physical browser/device, independent of user account.
    // Used to determine Host vs Peer role: only the device that created the
    // sync drive is the Host; all other devices (even same user) are Peers.
    _ensureDeviceId() {
        var id = localStorage.getItem('vx_sync_device_id');
        if (!id) {
            // Generate a random device ID: timestamp + random hex
            var arr = new Uint8Array(16);
            crypto.getRandomValues(arr);
            id = 'dev_' + Date.now().toString(36) + '_' + Array.from(arr).map(function(b) {
                return b.toString(16).padStart(2, '0');
            }).join('');
            localStorage.setItem('vx_sync_device_id', id);
            console.log('[SYNC] Generated new device_id: ' + id);
        } else {
            console.log('[SYNC] Existing device_id: ' + id);
        }
        return id;
    },

    getDeviceId() {
        return localStorage.getItem('vx_sync_device_id') || '';
    },

    // Load device name from server. If first time, server auto-assigns "#N".
    // Then prompts user to confirm or change the name.
    async _loadDeviceName() {
        var deviceId = this.getDeviceId();
        if (!deviceId) return;

        var cachedName = localStorage.getItem('vx_sync_device_name');
        if (cachedName) {
            this.deviceName = cachedName;
            this._deviceNameLoaded = true;
            this._updateDeviceNameDisplay();
        }

        try {
            var rsp = await this._post('device_get', { device_id: deviceId }, true);
            if (rsp.status === 1 && rsp.data && rsp.data.device_name) {
                this.deviceName = rsp.data.device_name;
                this._deviceNameLoaded = true;
                localStorage.setItem('vx_sync_device_name', this.deviceName);
                this._updateDeviceNameDisplay();

                // Check if this is a newly assigned default name (starts with #)
                var wasPrompted = localStorage.getItem('vx_sync_device_name_prompted');
                if (!wasPrompted && this.deviceName.charAt(0) === '#') {
                    localStorage.setItem('vx_sync_device_name_prompted', '1');
                    // Show prompt to let user set a custom name
                    this._showDeviceNamePrompt();
                }
            }
        } catch (e) {
            console.warn('[SYNC] Failed to load device name:', e);
        }
    },

    // Save device name to server
    async _saveDeviceName(name) {
        var deviceId = this.getDeviceId();
        if (!deviceId || !name) return false;

        try {
            var rsp = await this._post('device_set', {
                device_id: deviceId,
                device_name: name
            }, true);
            if (rsp.status === 1) {
                this.deviceName = name;
                localStorage.setItem('vx_sync_device_name', name);
                this._updateDeviceNameDisplay();
                console.log('[SYNC] Device name saved: ' + name);
                return true;
            }
        } catch (e) {
            console.warn('[SYNC] Failed to save device name:', e);
        }
        return false;
    },

    // Show the device name prompt modal
    _showDeviceNamePrompt() {
        var self = this;
        var currentName = this.deviceName || '#1';

        VXUI.openModal('sync-device-name-modal');

        var inputEl = document.getElementById('sync-device-name-input');
        var hintEl = document.getElementById('sync-device-name-hint');
        if (inputEl) {
            inputEl.value = currentName;
            inputEl.focus();
            inputEl.select();
        }
        if (hintEl) {
            hintEl.textContent = '当前设备名称：' + currentName + '。你可以直接使用或修改为自定义名称。';
        }

        var saveBtn = document.getElementById('sync-device-name-save');
        if (saveBtn) {
            saveBtn.onclick = async function() {
                var name = (inputEl ? inputEl.value : '').trim();
                if (!name) {
                    self.toastError(self._t('sync_device_name_empty'));
                    return;
                }
                saveBtn.disabled = true;
                saveBtn.textContent = '保存中...';
                var ok = await self._saveDeviceName(name);
                saveBtn.disabled = false;
                saveBtn.textContent = '保存';
                if (ok) {
                    VXUI.closeModal('sync-device-name-modal');
                    self.toastSuccess(self._t('sync_device_name_set').replace('{name}', name));
                } else {
                    self.toastError(self._t('sync_save_failed'));
                }
            };
        }
    },

    // Update device name display in the UI
    _updateDeviceNameDisplay() {
        var els = document.querySelectorAll('.vx-sync-device-chip-name');
        for (var i = 0; i < els.length; i++) {
            els[i].textContent = this.deviceName || '(未命名)';
        }
    },

    // Cancel device name modal (user chose to keep current name)
    cancelDeviceName() {
        VXUI.closeModal('sync-device-name-modal');
    },

    // Public: open the device name editor (can be called from UI button)
    editDeviceName() {
        this.trackUI('sync_edit_device_name');
        this._showDeviceNamePrompt();
    },

    destroy() {
        console.log('[SYNC] Module destroying, cleaning up connections');
        this._cleanupConnection();
        // Close notification WebSocket
        if (this.signalingWS) {
            this.signalingWS.onclose = null; // Prevent reconnect
            try { this.signalingWS.close(); } catch (e) {}
            this.signalingWS = null;
        }
        this._notifyReconnectDelay = 30000; // Prevent further reconnects
        // Reset module state so next init() starts fresh
        this._drivesLoaded = false;
        this._drivesLoadSucceeded = false;
        this._deviceNameLoaded = false;
        this.drives = [];
        this._myPendingRequests = [];
        this.currentDrive = null;
        this.isHost = false;
    },

    // ========== IndexedDB Folder Handle Persistence ==========
    async _openHandleDb() {
        if (typeof indexedDB === 'undefined') return null;
        if (this._handleDb) return this._handleDb;

        var self = this;
        return new Promise(function(resolve) {
            var req = indexedDB.open('tmplink_vxui_sync', 1);

            req.onupgradeneeded = function() {
                var db = req.result;
                if (!db.objectStoreNames.contains('folder_handle')) {
                    db.createObjectStore('folder_handle', { keyPath: 'id' });
                }
            };

            req.onsuccess = function() {
                self._handleDb = req.result;
                resolve(req.result);
            };

            req.onerror = function() {
                console.warn('[SYNC] IndexedDB open failed:', req.error);
                resolve(null);
            };
        });
    },

    async _saveFolderHandle(dirHandle, driveId) {
        try {
            var db = await this._openHandleDb();
            if (!db) return;

            var tx = db.transaction('folder_handle', 'readwrite');
            var store = tx.objectStore('folder_handle');
            // Store the actual FileSystemHandle (structured-cloneable) for restoration
            store.put({
                id: 'sync_host_folder_' + driveId,
                name: dirHandle.name,
                handle: dirHandle
            });

            console.log('[SYNC] Folder binding saved for drive ' + driveId + ': ' + dirHandle.name);
        } catch (e) {
            console.warn('[SYNC] Failed to save folder binding for drive ' + driveId + ':', e);
        }
    },

    async _restoreAndBindFolder(driveId) {
        try {
            var db = await this._openHandleDb();
            if (!db) return null;

            var self = this;
            return new Promise(function(resolve) {
                var tx = db.transaction('folder_handle', 'readonly');
                var store = tx.objectStore('folder_handle');
                var req = store.get('sync_host_folder_' + driveId);

                req.onsuccess = async function() {
                    var data = req.result;
                    if (!data || !data.name) {
                        console.log('[SYNC] No saved folder binding found for drive ' + driveId);
                        resolve(null);
                        return;
                    }

                    // If we have a stored handle, verify permission and use it
                    if (data.handle) {
                        try {
                            var perm = await data.handle.queryPermission({ mode: 'readwrite' });
                            if (perm === 'granted') {
                                console.log('[SYNC] Restored folder binding for drive ' + driveId + ': ' + data.name + ' (permission granted)');
                                self._boundFolder = {
                                    name: data.handle.name,
                                    handle: data.handle
                                };

                                // 多 session：同步写入 session 并获取文件夹锁文件
                                var session = self._getActiveSession();
                                if (session) {
                                    session.boundFolder = self._boundFolder;
                                    var locked = await self._acquireFolderLock(session);
                                    if (!locked) {
                                        console.warn('[SYNC] Folder lock acquisition failed for restored folder');
                                        VXUI.showMsg(self._t('sync_folder_locked_other_tab'), 'warning');
                                        self._boundFolder = null;
                                        session.boundFolder = null;
                                        self._updateFolderPathDisplay();
                                        resolve(null);
                                        return;
                                    }
                                    self._bcast('drive_locked', {
                                        drive_id: session.drive_id,
                                        role: session.role,
                                        folder_name: session.boundFolder.name
                                    });
                                }

                                self._updateFolderPathDisplay();
                                // Load persisted sync state from .tmpsync/state.json
                                self._loadSyncState();
                                // Phase 2 (A): begin native FS observation (no-op if unsupported)
                                self._startFSObserver();
                                resolve(data.name);
                                return;
                            }
                            // Try to request permission silently (may prompt user)
                            if (perm === 'prompt') {
                                console.log('[SYNC] Folder permission needs re-grant for drive ' + driveId + ': ' + data.name);
                                resolve(data.name);
                                return;
                            }
                        } catch (e) {
                            console.warn('[SYNC] Failed to verify folder permission:', e);
                        }
                    }

                    console.log('[SYNC] Found previous folder binding for drive ' + driveId + ': ' + data.name + ' (no handle or permission denied)');
                    resolve(data.name);
                };

                req.onerror = function() {
                    console.warn('[SYNC] Failed to read folder binding from IndexedDB for drive ' + driveId + ':', req.error);
                    resolve(null);
                };
            });
        } catch (e) {
            console.warn('[SYNC] Failed to restore folder binding for drive ' + driveId + ':', e);
            return null;
        }
    },

    async _removeStoredFolderHandle(driveId) {
        try {
            var db = await this._openHandleDb();
            if (!db) return;

            var tx = db.transaction('folder_handle', 'readwrite');
            var store = tx.objectStore('folder_handle');
            store.delete('sync_host_folder_' + driveId);
        } catch (e) {
            console.warn('[SYNC] Failed to remove stored folder handle for drive ' + driveId + ':', e);
        }
    },

    // ========== Backend API Integration (WebSocket-only) ==========
    
    // Request ID counter for matching requests to responses
    _wsRequestId: 0,
    // Pending WS requests: requestId -> { resolve, reject }
    _pendingWsRequests: {},

    /**
     * Send a request over the unified WSS connection and wait for a response.
     * @param {string} type - Message type (e.g., 'drive_list_req', 'sync_control')
     * @param {object} data - Request payload (will be sent as 'payload' field)
     * @param {boolean} silent - Suppress error toasts on failure
     * @returns {Promise<object>} Response data
     */
    async wsRequest(type, data, silent) {
        if (!this.signalingWS || this.signalingWS.readyState !== WebSocket.OPEN) {
            // If WSS is connecting, wait briefly
            if (this.signalingWS && this.signalingWS.readyState === WebSocket.CONNECTING) {
                var ok = await this._waitForWSS(5000);
                if (!ok) {
                    console.error('[SYNC] WSS still connecting for ' + type);
                    if (!silent) this.toastError(this._t('sync_network_error'));
                    return { status: 0, debug: 'wss_timeout' };
                }
            } else {
                console.error('[SYNC] WSS not connected for ' + type);
                if (!silent) this.toastError(this._t('sync_network_error'));
                return { status: 0, debug: 'wss_disconnected' };
            }
        }

        var requestId = ++this._wsRequestId;
        console.log('[SYNC] WSS request: ' + type + ' id=' + requestId);

        return new Promise((resolve) => {
            this._pendingWsRequests[requestId] = { resolve: resolve, silent: silent };

            // Build unified message format: {type, request_id, drive_id?, from_device?, to_device?, payload}
            var msg = { type: type, request_id: requestId, payload: data || {} };
            if (data) {
                if (data.drive_id) msg.drive_id = data.drive_id;
                if (data.from_device) msg.from_device = data.from_device;
                if (data.to_device) msg.to_device = data.to_device;
            }

            try {
                this.signalingWS.send(JSON.stringify(msg));
            } catch (e) {
                console.error('[SYNC] WSS send failed:', e);
                delete this._pendingWsRequests[requestId];
                if (!silent) this.toastError(this._t('sync_network_error'));
                resolve({ status: 0, debug: 'send_failed' });
            }

            var self = this;
            setTimeout(function() {
                if (self._pendingWsRequests[requestId]) {
                    console.warn('[SYNC] WSS request timeout: ' + type);
                    delete self._pendingWsRequests[requestId];
                    resolve({ status: 0, debug: 'timeout' });
                }
            }, 15000);
        });
    },

    /**
     * Wait for the WSS connection to reach OPEN state.
     */
    _waitForWSS(timeoutMs) {
        var self = this;
        return new Promise(function(resolve) {
            if (self.signalingWS && self.signalingWS.readyState === WebSocket.OPEN) {
                resolve(true);
                return;
            }
            var timer = setTimeout(function() {
                cleanup();
                resolve(false);
            }, timeoutMs);
            function onOpen() {
                cleanup();
                resolve(true);
            }
            function onClose() {
                cleanup();
                resolve(false);
            }
            function cleanup() {
                clearTimeout(timer);
                if (self.signalingWS) {
                    self.signalingWS.removeEventListener('open', onOpen);
                    self.signalingWS.removeEventListener('close', onClose);
                }
            }
            if (self.signalingWS) {
                self.signalingWS.addEventListener('open', onOpen);
                self.signalingWS.addEventListener('close', onClose);
            }
        });
    },

    /**
     * Send a sync_control message (P2P control message relay via WSS).
     * Online: direct push. Offline: stored for later retrieval.
     * @param {string} msgType - Control message type (e.g., 'file_list_req', 'sync_delta')
     * @param {string} toDevice - Target device ID ('*' for broadcast, 'host_xxx' or 'peer_xxx')
     * @param {object} payload - Message payload
     * @param {boolean} silent - Suppress error toasts
     * @returns {Promise<object>} Response with {delivered: bool}
     */
    async sendSyncControl(msgType, toDevice, payload, silent) {
        if (!this.currentDrive) {
            return { status: 0, debug: 'no_drive' };
        }
        var fromDevice = this._getPersistentDeviceId();

        // wsRequest wraps the entire `data` object as msg.payload, so all
        // payload fields (including _msg_type) must be at the top level of
        // `data` — NOT nested inside data.payload. The server reads _msg_type
        // from the top level of msg.Payload to determine the actual message
        // type for routing and offline storage.
        var data = Object.assign({}, payload || {}, {
            _msg_type: msgType,
            drive_id: this.currentDrive.drive_id,
            from_device: fromDevice,
            to_device: toDevice
        });

        return await this.wsRequest('sync_control', data, silent);
    },

    /**
     * Handle a response from the server for a pending WS request.
     */
    handleWsResponse(requestId, data) {
        var pending = this._pendingWsRequests[requestId];
        if (!pending) return;
        
        delete this._pendingWsRequests[requestId];
        
        // Convert to REST-like response format for backward compatibility
        var hasError = data.error !== undefined || (data.status && data.status === 0);
        var response = {
            status: hasError ? 0 : 1,
            data: hasError ? null : data,
            debug: hasError ? (data.error || 'unknown error') : null
        };
        
        if (!hasError) {
            console.log('[SYNC] WS response: request_id=' + requestId);
        } else {
            if (!pending.silent) {
                this.toastError(data.error || this._t('sync_request_failed'));
            }
            // Special handling: if drive_enter returns no_permission, cleanup and return to drive list
            if (data.error === 'no_permission' && this.currentDrive) {
                console.warn('[SYNC] Permission denied for drive, cleaning up and returning to list');
                this.hideLoading();
                this._cleanupConnection();
                this._boundFolder = null;
                this.isHost = false;
                this.currentDrive = null;
                // Show drive list and hide detail/lobby
                document.getElementById('sync-drive-list').style.display = '';
                document.getElementById('sync-drive-detail').style.display = 'none';
                document.getElementById('sync-drive-lobby').style.display = 'none';
                // Reload drives to remove the expired/unauthorized one
                this.loadDrives();
                // Show friendly message
                this.toastError(this._t('sync_no_permission_error'));
            }
        }
        
        pending.resolve(response);
    },

    async _post(action, data, silent) {
        // Map legacy action names to unified WSS message types.
        // All operations go through the single signalingWS (/ws) connection.
        var wsType = '';
        switch (action) {
            case 'device_get':
                wsType = 'device_get_req';
                break;
            case 'device_set':
                wsType = 'device_set_req';
                break;
            case 'drive_list':
                wsType = 'drive_list_req';
                break;
            case 'drive_create':
                wsType = 'drive_create_req';
                break;
            case 'drive_join':
                wsType = 'drive_join_req';
                break;
            case 'drive_delete':
                wsType = 'drive_delete_req';
                break;
            case 'drive_enter':
                wsType = 'drive_enter';
                break;
            case 'drive_leave':
                wsType = 'drive_leave';
                break;
            case 'file_delete':
            case 'file_mkdir':
            case 'file_rename':
            case 'file_move':
                // File operations now go through sync_control (P2P relay).
                // The caller wraps the action in a sync_control message.
                var fileOpAction = action.replace('file_', '');
                data.action = fileOpAction;
                return this.sendSyncControl('file_op', '*', data, silent);
            case 'p2p_message':
                // Legacy: now use sendSyncControl directly.
                return this.sendSyncControl(data.msg_type, data.to_device, data.payload, silent);
            case 'p2p_poll':
                // Offline message poll — uses dedicated offline_poll_req type.
                return this.wsRequest('offline_poll_req', {
                    drive_id: data.drive_id,
                    from_device: this._getPersistentDeviceId()
                }, silent);
            default:
                console.warn('[SYNC] Unknown action for WS: ' + action);
                return { status: 0, debug: 'unknown_action' };
        }

        var rsp = await this.wsRequest(wsType, data || {}, silent);
        return rsp;
    },

    // ========== P2P Control Message Relay (via API) ==========
    // File chunks go through WebRTC DataChannel (P2P or WSS relay).
    // All control messages (file lists, sync deltas, chunk metadata) go through sync_server API.

    _getPersistentDeviceId() {
        return (this.isHost ? 'host_' : 'peer_') + this.getDeviceId();
    },

    _getHostPersistentId() {
        return 'host_' + (this.currentDrive ? this.currentDrive.host_device_id : '');
    },

    _getAllPeerDeviceIds() {
        // Returns all peer persistent device IDs this Host is connected to.
        // The peer_id from the notification is already in the format 'peer_dev_xxx'.
        var ids = [];
        if (this._peerDeviceIds) {
            Object.keys(this._peerDeviceIds).forEach(function(uid) {
                ids.push(VX_SYNC._peerDeviceIds[uid]);
            });
        }
        return ids;
    },

    async sendToAllPeers(msgType, payload) {
        var peerIds = this._getAllPeerDeviceIds();
        // Send in parallel — sequential await would compound WS timeouts
        // (e.g., 3 peers × 15s timeout = 45s before the last peer is reached).
        await Promise.all(peerIds.map(function(id) {
            return VX_SYNC.sendP2PMessage(msgType, id, payload);
        }));
    },

    async sendP2PMessage(msgType, toDevice, payload) {
        if (!this.currentDrive) return;
        var fromDevice = this._getPersistentDeviceId();
        console.log('[SYNC] sync_control send: type=' + msgType + ' from=' + fromDevice + ' to=' + toDevice);
        return await this.sendSyncControl(msgType, toDevice, payload, true);
    },

    async pollP2PMessages() {
        // Offline messages are auto-delivered on reconnect via WSS.
        // This poll is a one-time recovery for any missed messages.
        if (!this.currentDrive || !this._p2pPollActive) return;
        var deviceId = this._getPersistentDeviceId();
        try {
            var rsp = await this.wsRequest('offline_poll_req', {
                drive_id: this.currentDrive.drive_id,
                from_device: deviceId
            }, true);
            if (rsp && rsp.status === 1 && rsp.data && rsp.data.messages) {
                var msgs = rsp.data.messages;
                if (msgs.length > 0) {
                    console.log('[SYNC] Offline poll: received ' + msgs.length + ' messages');
                }
                for (var i = 0; i < msgs.length; i++) {
                    this.handleP2PMessage(msgs[i]);
                }
            }
        } catch (e) {
            // Silently ignore poll errors
        }
    },

    startP2PPoll() {
        // Messages are now delivered directly via the persistent notification WSS.
        // This method is kept for one-time recovery polls (e.g., after reconnection).
        this._p2pPollActive = true;
        this.pollP2PMessages();
    },

    stopP2PPoll() {
        this._p2pPollActive = false;
        if (this._p2pPollTimer) {
            clearInterval(this._p2pPollTimer);
            this._p2pPollTimer = null;
        }
    },

    // handleP2PMessage processes control messages delivered via the persistent
    // notification WSS (primary path) or API poll (recovery path).
    // These replace the DataChannel-based control messages for file_list_resp,
    // peer_file_report, sync_delta, and file_report_req.
    handleP2PMessage(msg) {
        var payload = msg.payload;
        if (typeof payload === 'string') {
            try { payload = JSON.parse(payload); } catch(e) { return; }
        }
        var msgType = msg.msg_type;
        // For sync_control relay, the actual message type is in payload._msg_type
        if (msgType === 'sync_control' && payload && payload._msg_type) {
            msgType = payload._msg_type;
        }
        console.log('[SYNC] P2P message: type=' + msgType + ' from=' + msg.from_device);

        switch (msgType) {
            case 'file_list_resp':
                if (this.isHost) break;
                var respCount = payload.files ? payload.files.length : 0;
                var respPath = payload.path || '/';
                console.log('[SYNC] Received file_list_resp via WSS: ' + respCount + ' files at ' + respPath);
                if (this._connectTimeout) { clearTimeout(this._connectTimeout); this._connectTimeout = null; }
                this.updateLoadingProgress('连接成功', '已加载 ' + respCount + ' 个文件', 100);
                this.hideLoading();
                if (respPath === this.currentPath) {
                    var respFiles = payload.files || [];
                    this.fileCache.clear();
                    respFiles.forEach(function(f) { VX_SYNC.fileCache.set(f.sha1, f); });
                    this.renderFileList(respFiles);
                    this.updateBreadcrumb();
                }
                // Phase 3 (C): re-report local state so host can compute a fresh delta
                this._schedulePeerReport();
                break;

            case 'file_list_req':
                // Host: Peer is requesting file list at a specific path
                if (!this.isHost) break;
                var reqPath = payload.path || '/';
                console.log('[SYNC] Received file_list_req via WSS for path: ' + reqPath);
                var hostSelf = this;
                this._listDirectoryAt(reqPath).then(function(files) {
                    console.log('[SYNC] Host responding file_list_req: ' + files.length + ' files at ' + reqPath);
                    hostSelf.sendToAllPeers('file_list_resp', { files: files, path: reqPath });
                }).catch(function(e) {
                    console.warn('[SYNC] Host failed to list directory for peer:', e);
                    hostSelf.sendToAllPeers('file_list_resp', { files: [], path: reqPath });
                });
                break;

            case 'peer_file_report':
                if (!this.isHost) break;
                console.log('[SYNC] Received peer_file_report via WSS: ' + (payload.files ? payload.files.length : 0) + ' files, ' + (payload.deleted ? payload.deleted.length : 0) + ' deleted' + (payload.folder_changed ? ' (folder changed)' : ''));
                this.handlePeerFileReport(payload.files || [], payload.deleted || [], msg.from_device, payload.folder_changed === true);
                break;

            case 'file_report_req':
                if (this.isHost) break;
                console.log('[SYNC] Received file_report_req via WSS');
                this.sendPeerFileReport();
                break;

            case 'sync_delta':
                if (this.isHost) break;
                console.log('[SYNC] Processing sync_delta via WSS');
                this.processDelta(payload, msg.from_device);
                // Phase 3 (C): after applying the delta, re-report so the host can
                // confirm convergence or send follow-up work without waiting
                this._schedulePeerReport();
                break;

            case 'file_op':
                // Remote file operation (delete/mkdir/rename/move) received via WSS.
                // Skip self-echo: the Host broadcasts to all peers via sendToAllPeers,
                // but the server may also relay the message back to the sender.
                var myDeviceId = this._getPersistentDeviceId();
                if (msg.from_device === myDeviceId) {
                    console.log('[SYNC] Skipping self file_op echo');
                    break;
                }
                this._handleRemoteFileOp(payload, msg.from_device);
                break;

            default:
                console.log('[SYNC] Unhandled P2P message type: ' + msgType);
        }
    },

    // Dispatch a remote file_op message to the appropriate handler.
    async _handleRemoteFileOp(payload, fromDevice) {
        var action = payload.action;
        var source = this._getDeviceDisplayName(fromDevice) || '';
        if (action === 'delete') {
            console.log('[SYNC] Remote file_op delete: sha1=' + payload.sha1);
            await this.handleRemoteDelete(payload.sha1, source);
        } else if (action === 'mkdir') {
            console.log('[SYNC] Remote file_op mkdir:', payload.name);
            await this.handleRemoteMkdir(payload, source);
        } else if (action === 'rename') {
            console.log('[SYNC] Remote file_op rename: sha1=' + payload.sha1 + ' -> ' + payload.new_name);
            this.handleRemoteRename(payload.sha1, payload.new_name, payload.new_sha1, source);
        } else if (action === 'move') {
            console.log('[SYNC] Remote file_op move: sha1=' + payload.sha1 + ' -> ' + payload.new_parent_path);
            this.handleRemoteMove(payload.sha1, payload.new_parent_path, payload.new_sha1, source);
        } else {
            console.warn('[SYNC] Unknown file_op action: ' + action);
        }
    },

    // Get human-readable display name for a device ID.
    _getDeviceDisplayName(deviceId) {
        if (!deviceId) return '';
        // Check _peerConnections first (Host side)
        if (this._peerConnections && this._peerConnections[deviceId]) {
            return this._peerConnections[deviceId].displayName || deviceId;
        }
        // Check peers list
        if (this.peers) {
            for (var i = 0; i < this.peers.length; i++) {
                if (this.peers[i].device_id === deviceId || this.peers[i].peer_id === deviceId) {
                    return this.peers[i].device_name || deviceId;
                }
            }
        }
        // Check if this is the Host (for Peer side)
        if (this.currentDrive && this.currentDrive.host_device === deviceId) {
            return this.currentDrive.host_device_name || '主机';
        }
        return deviceId;
    },

    // Get the Host device's display name for the current drive.
    // Used by the Peer to show meaningful connection activity messages.
    _getHostDisplayName() {
        if (this.currentDrive && this.currentDrive.host_device_name) {
            return this.currentDrive.host_device_name;
        }
        // Fallback: search the peer list for the Host entry
        if (this.peers) {
            for (var i = 0; i < this.peers.length; i++) {
                if (this.peers[i].role === 'host') {
                    return this.peers[i].device_name || '主机';
                }
            }
        }
        return '主机';
    },
    
    async loadDrives() {
        this.trackUI('sync_load_drives');
        if (!TL.api_token) {
            console.warn('[SYNC] loadDrives skipped: no api_token');
            this._drivesLoaded = true;
            this.renderDriveList();
            return;
        }
        
        console.log('[SYNC] Loading drive list...');
        this.showLoading('正在加载同步盘列表...');
        const rsp = await this._post('drive_list');
        this.hideLoading();
        
        this._drivesLoaded = true;
        if (rsp.status === 1 && rsp.data) {
            this.drives = rsp.data;
            this._drivesLoadSucceeded = true;
            console.log('[SYNC] Loaded ' + rsp.data.length + ' drives');
        } else {
            console.warn('[SYNC] loadDrives returned status=' + (rsp ? rsp.status : 'null'));
            this.drives = [];
        }
        this.renderDriveList();
        this.loadUnreadCount();
        // Also load the applicant's own pending join requests so the
        // "审核中" / "可加入" cards render (and persist across reloads).
        this.loadMyJoinRequests();
    },

    // Fetch the applicant's own join requests (pending/approved/rejected)
    // and merge them into the drive-list rendering as pending-review cards.
    async loadMyJoinRequests() {
        if (!TL.api_token) return;
        try {
            const resp = await this.wsRequest('my_join_requests_req', {});
            if (resp.status !== 1) return;
            var list = (resp.data && resp.data.requests) || [];
            // Drop requests whose drive already appears in the joined list
            // (e.g. the applicant already joined after approval).
            var self = this;
            list = list.filter(function(r) {
                return !self.drives.some(function(d) { return d.drive_id === r.drive_id; });
            });
            this._myPendingRequests = list;
            this.renderDriveList();
        } catch (e) {
            console.warn('[SYNC] loadMyJoinRequests failed', e);
        }
    },

    // Real-time status update pushed by the backend when a host
    // approves/rejects the applicant's join request. The payload carries
    // { request_id, status, drive_name }. We refresh from the server so the
    // card reflects the authoritative state.
    _handleJoinRequestStatus(msg) {
        var payload = msg.payload || {};
        if (typeof payload === 'string') {
            try { payload = JSON.parse(payload); } catch(e) { return; }
        }
        // BroadcastToUser puts extra fields at top level — merge msg + payload.
        var status = payload.status || msg.status;
        var driveName = payload.drive_name || msg.drive_name || '';
        console.log('[SYNC] join_request_status: drive=' + msg.drive_id + ' status=' + status);

        // Optimistically update the local pending card so the UI reacts
        // instantly, then re-fetch authoritative state.
        var driveId = msg.drive_id;
        for (var i = 0; i < this._myPendingRequests.length; i++) {
            if (this._myPendingRequests[i].drive_id === driveId) {
                this._myPendingRequests[i].status = status;
                if (driveName) {
                    this._myPendingRequests[i].drive_name = driveName;
                }
                break;
            }
        }
        this.renderDriveList();

        if (status === 'approved') {
            VXUI.showMsg(this._t('sync_join_approved_tip').replace('{name}', driveName || ''), 'success');
        } else if (status === 'rejected') {
            VXUI.showMsg(this._t('sync_join_rejected_tip').replace('{name}', driveName || ''), 'warn');
        }

        // Refresh notifications + authoritative pending list.
        this.loadUnreadCount();
        var self = this;
        setTimeout(function() { self.loadMyJoinRequests(); }, 500);
    },

    // Enter a drive from an approved pending card. The applicant already has
    // an approved join_request record, so drive_enter's permission check will
    // pass without needing a drive_key.
    async joinApprovedDrive(driveId) {
        var req = this._myPendingRequests.find(function(r) { return r.drive_id === driveId; });
        if (!req || req.status !== 'approved') {
            VXUI.showMsg(this._t('sync_join_not_approved'), 'error');
            return;
        }
        // Build a minimal drive object and inject it into this.drives so
        // enterDrive() can find it.
        var drive = {
            drive_id: req.drive_id,
            name: req.drive_name,
            host_uid: req.host_uid,
            host_device_id: req.host_device_id,
            peer_count: 0,
            peer_limit: 10,
            host_online: req.host_online,
            created_at: req.created_at,
            server_addr: req.server_addr || ''
        };
        this.drives = this.drives.filter(function(d) { return d.drive_id !== drive.drive_id; });
        this.drives.unshift(drive);
        // Remove the pending card — the drive now appears as a normal card.
        this._myPendingRequests = this._myPendingRequests.filter(function(r) { return r.drive_id !== driveId; });
        this.renderDriveList();
        // Enter the drive as a Peer.
        this.enterDrive(driveId);
    },

    // Dismiss a rejected pending card from the drive list.
    dismissMyPendingRequest(driveId) {
        this._myPendingRequests = this._myPendingRequests.filter(function(r) { return r.drive_id !== driveId; });
        this.renderDriveList();
    },

    async createDrive(name) {
        this.trackUI('sync_create_drive');
        console.log('[SYNC] Creating drive: name="' + (name || '(default)') + '"');
        const rsp = await this._post('drive_create', {
            drive_name: name || '',
            device_id: this.getDeviceId()
        });
        
        if (rsp.status === 1) {
            this.currentDrive = rsp.data;
            this.isHost = true;  // Creator device is always Host
            this._hostOnline = true;
            console.log('[SYNC] Drive created: id=' + rsp.data.drive_id + ' host_device_id=' + rsp.data.host_device_id + ' server_addr=' + (rsp.data.server_addr || 'none'));
            this.addActivity('create_drive', (rsp.data.name || rsp.data.drive_name || '同步盘'));
            // Enter drive directly (will prompt folder selection then start server)
            this.fileCache.clear();
            this.currentPath = '/';
            this.peers = [];
            this._boundFolder = null;
            this._cleanupConnection();
            // Add new drive to local list and refresh UI (convert field names to match drive_list format)
            var newDrive = {
                drive_id: rsp.data.drive_id,
                name: rsp.data.drive_name || rsp.data.name || '',
                host_uid: rsp.data.host_uid,
                host_device_id: rsp.data.host_device_id,
                peer_count: 0,
                peer_limit: rsp.data.peer_limit || this._getPeerLimit(),
                host_online: 0,
                created_at: new Date().toISOString().replace('T', ' ').substring(0, 19),
                server_addr: rsp.data.server_addr || ''
            };
            // Remove if already exists (shouldn't happen, but be safe)
            this.drives = this.drives.filter(function(d) { return d.drive_id !== newDrive.drive_id; });
            this.drives.unshift(newDrive);
            this.renderDriveList();
            this.startServer();
        } else {
            console.warn('[SYNC] createDrive failed: ' + (rsp.debug || 'unknown'));
            this.toastError(this._quotaError(rsp.debug, 'drive_limit_reached', 'sync_drive_limit_reached', 'sync_create_failed'));
        }
    },
    
    async joinDrive(driveKey) {
        if (!driveKey || !driveKey.trim()) {
            this.toastWarning(this._t('sync_password_required'));
            return;
        }
        
        this.trackUI('sync_join_drive');
        console.log('[SYNC] Joining drive with key: ' + (driveKey ? driveKey.substring(0, 8) + '...' : 'empty'));
        this.showLoading('正在加入同步盘...');
        const rsp = await this._post('drive_join', {
            drive_key: driveKey.trim(),
            device_id: this.getDeviceId()
        });
        this.hideLoading();
        
        if (rsp.status === 1) {
            this.currentDrive = rsp.data;
            this.isHost = false;
            this._hostOnline = (rsp.data.host_online === 1 || rsp.data.host_online === true);
            if (rsp.data.server_addr) {
                this.serverAddr = rsp.data.server_addr;
            }
            console.log('[SYNC] Joined drive: id=' + rsp.data.drive_id + ' host_online=' + this._hostOnline + ' server_addr=' + (rsp.data.server_addr || 'none'));
            this.addActivity('join_drive', (rsp.data.name || rsp.data.drive_name || '同步盘'));
            // Enter drive directly (will prompt folder selection then connect to Host)
            this.fileCache.clear();
            this.currentPath = '/';
            this.peers = [];
            this._boundFolder = null;
            this._cleanupConnection();
            // Update local drive list with joined drive (convert field names to match drive_list format)
            var joinedDrive = {
                drive_id: rsp.data.drive_id,
                name: rsp.data.drive_name || rsp.data.name || '',
                host_uid: rsp.data.host_uid,
                host_device_id: rsp.data.host_device_id,
                peer_count: 0,
                peer_limit: rsp.data.peer_limit || 10,
                host_online: rsp.data.host_online ? 1 : 0,
                created_at: new Date().toISOString().replace('T', ' ').substring(0, 19),
                server_addr: rsp.data.server_addr || ''
            };
            this.drives = this.drives.filter(function(d) { return d.drive_id !== joinedDrive.drive_id; });
            this.drives.unshift(joinedDrive);
            this.renderDriveList();
            if (this._hostOnline) {
                this.connectToHost();
            } else {
                this.showLobby();
            }
        } else {
            console.warn('[SYNC] joinDrive failed: ' + (rsp.debug || 'unknown'));
            this.toastError(this._quotaError(rsp.debug, 'device_limit_reached', 'sync_device_limit_reached', 'sync_join_failed'));
        }
    },
    
    async listFiles(path) {
        if (!this.currentDrive) return;

        if (path !== undefined && path !== null && path !== '') {
            this.currentPath = path;
        }
        console.log('[SYNC] Listing files: path=' + this.currentPath + ' isHost=' + this.isHost);
        this.showLoading('正在加载文件列表...');

        if (this.isHost) {
            // Host: read directly from bound folder in real-time
            var files = await this._listDirectoryAt(this.currentPath);
            this.hideLoading();
            console.log('[SYNC] File list: ' + files.length + ' items at ' + this.currentPath);
            this.fileCache.clear();
            files.forEach(f => this.fileCache.set(f.sha1, f));
            this.renderFileList(files);
            this.updateBreadcrumb();
        } else {
            // Peer: scan local bound folder + request remote file list from Host
            try {
                this._localFiles = await this._listDirectoryAt(this.currentPath);
            } catch(e) {
                console.warn('[SYNC] Local scan failed at ' + this.currentPath + ':', e);
                this._localFiles = [];
            }
            // Render local files immediately (pending_upload status)
            this.renderFileList(Array.from(this.fileCache.values()));
            this.updateBreadcrumb();
            // Request remote file list from Host
            this.sendP2PMessage('file_list_req', this._getHostPersistentId(), { path: this.currentPath });
            // Response will be handled by file_list_resp handler (re-renders with merged data)
            this.hideLoading();
        }
    },
    
    async requestSyncDelta() {
        if (!this.currentDrive || !this.isHost) return;
        
        // Scan bound folder to get current file list for sync comparison
        var clientFiles = [];
        if (this._boundFolder && this._boundFolder.handle) {
            try {
                var allFiles = await this.getBoundFolderFiles();
                for (var i = 0; i < allFiles.length; i++) {
                    var f = allFiles[i];
                    if (f.is_dir) continue; // Only sync files, not directories
                    var sha1 = await this._fingerprintFile(f.name, f.path, f.size, f.mtime);
                    clientFiles.push({ sha1: sha1, mtime: f.mtime });
                }
            } catch (e) {
                console.warn('[SYNC] Failed to scan folder for sync delta:', e);
            }
        }
        
        console.log('[SYNC] Requesting sync delta: ' + clientFiles.length + ' local files');
        const rsp = await this._post('sync_delta', {
            drive_id: this.currentDrive.drive_id,
            files: JSON.stringify(clientFiles)
        });
        
        if (rsp.status === 1 && rsp.data) {
            console.log('[SYNC] Sync delta received: ' + JSON.stringify(rsp.data).substring(0, 200));
            this.processDelta(rsp.data, '');
        }
    },
    
    // ========== Bidirectional Sync: Peer → Host ==========
    // folderChanged: true when Peer just switched bound folder. In that case
    // Peer's _peerLastPaths has been reset, so no deletions are detected; the
    // flag tells Host to also reset its record of what Peer had, so Host does
    // NOT propagate "missing on Peer" as deletions to itself. Instead Host's
    // files are treated as new files Peer should download.
    async sendPeerFileReport(folderChanged) {
        if (this.isHost) return;
        if (!this._boundFolder || !this._boundFolder.handle) {
            console.log('[SYNC] Peer has no bound folder, skipping file report');
            return;
        }
        // Skip if a transfer is still in progress (avoid triggering new delta mid-transfer)
        if (this._transferBusy || this._downloads.size > 0) {
            console.log('[SYNC] Skipping file report: transfer in progress');
            return;
        }
        // Skip if there are pending downloads (files requested but not yet saved).
        // Reporting now would send stale state and cause the Host to re-send the
        // same files in an infinite loop.
        if (this._pendingDownloads && this._pendingDownloads.size > 0) {
            console.log('[SYNC] Skipping file report: ' + this._pendingDownloads.size + ' downloads pending');
            return;
        }

        try {
            var allFiles = await this.getBoundFolderFiles();
            var report = [];
            var currentPaths = {};
            for (var i = 0; i < allFiles.length; i++) {
                var f = allFiles[i];
                if (f.is_dir) continue;
                var sha1 = await this._fingerprintFile(f.name, f.parent_path, f.size, f.mtime);
                var filePath = (f.parent_path === '/' ? '' : f.parent_path) + '/' + f.name;
                currentPaths[filePath] = true;
                report.push({
                    sha1: sha1,
                    name: f.name,
                    size: f.size,
                    mtime: f.mtime,
                    parent_path: f.parent_path || '/'
                });
            }

            // Detect deletions: paths that existed last sync but not now
            var deletedFiles = [];
            if (this._peerLastPaths) {
                for (var prevPath in this._peerLastPaths) {
                    if (!currentPaths[prevPath]) {
                        deletedFiles.push(prevPath);
                    }
                }
            }

            // Update last-known state for next cycle
            this._peerLastPaths = currentPaths;

            // Record each detected deletion in activity list
            for (var di = 0; di < deletedFiles.length; di++) {
                var dname = deletedFiles[di].split('/').pop();
                this.addActivity('delete', dname, { source: this._t('sync_this_device'), target: this._t('sync_role_host') });
            }

            console.log('[SYNC] Peer sending file report to Host: ' + report.length + ' files, ' + deletedFiles.length + ' deleted' + (folderChanged ? ' (folder changed)' : ''));
            this.sendP2PMessage('peer_file_report', this._getHostPersistentId(), { files: report, deleted: deletedFiles, folder_changed: !!folderChanged });
            // Persist state to .tmpsync/state.json
            this._saveSyncState();
        } catch (e) {
            console.warn('[SYNC] Failed to send peer file report:', e);
        }
    },
    
    // Periodic re-scan for bidirectional sync with dynamic interval adjustment.
    // Min interval: 3s (when changes detected), Max interval: 60s (when idle).
    // Interval doubles after each no-change scan, resets to min on any change.
    startPeriodicSync() {
        this.stopPeriodicSync();
        this._syncNoChangeCount = 0;
        this._lastScanFingerprints = null;

        if (this._fsObserverSupported) {
            // FileSystemObserver is available — it delivers sub-second change
            // notifications. We start it and use a long-interval safety-net
            // scan (120s) only to catch any events the observer might miss.
            this._startFSObserver();
            this._syncInterval = 120000; // 120s safety net
            this._syncMinInterval = 120000;
            this._syncMaxInterval = 120000;
            console.log('[SYNC] Periodic sync started (FileSystemObserver active, safety-net scan every 120s)');
        } else {
            // FileSystemObserver unavailable — fall back to polling with
            // dynamic interval adjustment (1s-60s based on file count).
            this._syncInterval = 3000;
            this._syncMinInterval = 3000;
            this._syncMaxInterval = 60000;
            console.log('[SYNC] Periodic sync started (FileSystemObserver unavailable — polling only, dynamic interval 3s-60s)');
        }
        this._scheduleNextSync();
    },

    _scheduleNextSync() {
        if (!this.currentDrive) return;
        var self = this;
        this._syncTimer = setTimeout(function() {
            self._doPeriodicScan();
        }, this._syncInterval);
    },
    
    async _doPeriodicScan() {
        if (!this.currentDrive) return;
        if (this._scanInProgress) {
            // Previous scan still running, skip this cycle but keep scheduling
            this._scheduleNextSync();
            return;
        }
        this._scanInProgress = true;
        var self = this;
        
        if (this.isHost) {
            // Host: scan local files, detect changes, send to Peers
            try {
                var files = await this._listDirectoryAt(this.currentPath);
                var changed = this._detectScanChanges(files);
                // Detect deletions: files in cache but not in current scan
                var oldCache = Array.from(this.fileCache.values());
                var newPaths = {};
                files.forEach(function(f) { newPaths[f.sha1] = true; });
                for (var di = 0; di < oldCache.length; di++) {
                    if (!newPaths[oldCache[di].sha1]) {
                        self.addActivity('delete', oldCache[di].name, { source: self._t('sync_this_device'), target: self._t('sync_all_peers') });
                        // Track as pending Host deletion to prevent race condition
                        var delPath = (oldCache[di].parent_path === '/' ? '' : oldCache[di].parent_path) + '/' + oldCache[di].name;
                        if (!self._hostPendingOps) self._hostPendingOps = {};
                        self._hostPendingOps[delPath] = { op: 'delete', ts: Date.now() };
                    }
                }
                // Update Host's own file cache and UI
                this.fileCache.clear();
                files.forEach(function(f) { self.fileCache.set(f.sha1, f); });
                this.renderFileList(files);
                this.updateBreadcrumb();
                // Push to Peers via WSS
                this.sendToAllPeers('file_list_resp', { files: files, path: this.currentPath });
                this._adjustSyncInterval(changed, files.length);
            } catch (e) {
                console.warn('[SYNC] Host periodic scan failed:', e);
                this._adjustSyncInterval(false, 0);
            }
        } else {
            // Peer: scan local files, send report to Host
            try {
                var allFiles = await this.getBoundFolderFiles();
                var report = [];
                var currentPaths = {};
                for (var i = 0; i < allFiles.length; i++) {
                    var f = allFiles[i];
                    if (f.is_dir) continue;
                    var sha1 = await this._fingerprintFile(f.name, f.parent_path, f.size, f.mtime);
                    var filePath = (f.parent_path === '/' ? '' : f.parent_path) + '/' + f.name;
                    currentPaths[filePath] = true;
                    report.push({
                        sha1: sha1,
                        name: f.name,
                        size: f.size,
                        mtime: f.mtime,
                        parent_path: f.parent_path || '/'
                    });
                }
                
                // Detect deletions
                var deletedFiles = [];
                if (this._peerLastPaths) {
                    for (var prevPath in this._peerLastPaths) {
                        if (!currentPaths[prevPath]) {
                            deletedFiles.push(prevPath);
                        }
                    }
                }
                this._peerLastPaths = currentPaths;
                
                // Record each detected deletion in activity list
                for (var di = 0; di < deletedFiles.length; di++) {
                    var dname = deletedFiles[di].split('/').pop();
                    this.addActivity('delete', dname, { source: this._t('sync_this_device'), target: this._t('sync_role_host') });
                }

                // Detect changes by comparing fingerprints
                var changed = this._detectScanChanges(report);

                // Skip sending peer_file_report if downloads are pending —
                // reporting stale state causes the Host to re-send the same files
                if (this._pendingDownloads && this._pendingDownloads.size > 0) {
                    console.log('[SYNC] Periodic scan: skipping report, ' + this._pendingDownloads.size + ' downloads pending');
                } else {
                    this.sendP2PMessage('peer_file_report', this._getHostPersistentId(), {
                        files: report,
                        deleted: deletedFiles
                    });
                }

                // Also refresh local files at current path for merged UI
                try {
                    this._localFiles = await this._listDirectoryAt(this.currentPath);
                    this.renderFileList(Array.from(this.fileCache.values()));
                } catch(le) {
                    // local path may not exist yet, that's OK
                }

                this._adjustSyncInterval(changed, report.length);
            } catch (e) {
                console.warn('[SYNC] Peer periodic scan failed:', e);
                this._adjustSyncInterval(false, 0);
            }
        }
        
        this._scanInProgress = false;
        this._scheduleNextSync();
    },
    
    // Compare current file list with last scan to detect changes.
    // Returns true if any file was added, removed, or modified.
    _detectScanChanges(currentFiles) {
        var currentFingerprints = {};
        for (var i = 0; i < currentFiles.length; i++) {
            var f = currentFiles[i];
            var path = (f.parent_path === '/' ? '' : f.parent_path) + '/' + f.name;
            currentFingerprints[path] = f.sha1 || (f.size + '_' + f.mtime);
        }
        
        if (!this._lastScanFingerprints) {
            this._lastScanFingerprints = currentFingerprints;
            return false; // First scan, no baseline to compare
        }
        
        var changed = false;
        var lastKeys = Object.keys(this._lastScanFingerprints);
        var currKeys = Object.keys(currentFingerprints);
        
        // Check for added or removed files
        if (lastKeys.length !== currKeys.length) {
            changed = true;
        } else {
            // Check for modified files (same path, different fingerprint)
            for (var path in currentFingerprints) {
                if (this._lastScanFingerprints[path] !== currentFingerprints[path]) {
                    changed = true;
                    break;
                }
            }
        }
        
        this._lastScanFingerprints = currentFingerprints;
        return changed;
    },
    
    // Adjust scan interval: reset to min on changes, double on no changes (up to max).
    // fileCount is used to dynamically scale min/max intervals: fewer files → faster scans.
    // When FileSystemObserver is active, this is a no-op — the safety-net scan
    // uses a fixed 120s interval and change detection is handled by the observer.
    _adjustSyncInterval(changed, fileCount) {
        if (this._fsObserverSupported) {
            // Fixed safety-net interval, no dynamic adjustment needed
            return;
        }

        // Calculate dynamic min/max based on file count
        fileCount = fileCount || 0;
        var minInt, maxInt;
        if (fileCount <= 5) {
            minInt = 1000;  maxInt = 15000;  // 1s-15s
        } else if (fileCount <= 20) {
            minInt = 2000;  maxInt = 30000;  // 2s-30s
        } else if (fileCount <= 50) {
            minInt = 3000;  maxInt = 45000;  // 3s-45s
        } else if (fileCount <= 200) {
            minInt = 5000;  maxInt = 60000;  // 5s-60s
        } else {
            minInt = 10000; maxInt = 60000;  // 10s-60s
        }

        if (changed) {
            this._syncMinInterval = minInt;
            this._syncMaxInterval = maxInt;
            this._syncInterval = minInt;
            this._syncNoChangeCount = 0;
            console.log('[SYNC] Changes detected (files: ' + fileCount + '), reset scan interval to ' + (this._syncInterval / 1000) + 's (range: ' + (minInt / 1000) + 's-' + (maxInt / 1000) + 's)');
        } else {
            this._syncMinInterval = minInt;
            this._syncMaxInterval = maxInt;
            this._syncNoChangeCount++;
            // Double the interval each time, capped at max
            var newInterval = Math.min(minInt * Math.pow(2, this._syncNoChangeCount), maxInt);
            if (newInterval !== this._syncInterval) {
                this._syncInterval = newInterval;
                console.log('[SYNC] No changes for ' + this._syncNoChangeCount + ' scans (files: ' + fileCount + '), increased interval to ' + (this._syncInterval / 1000) + 's (range: ' + (minInt / 1000) + 's-' + (maxInt / 1000) + 's)');
            }
        }
    },
    
    stopPeriodicSync() {
        if (this._syncTimer) {
            clearTimeout(this._syncTimer);
            this._syncTimer = null;
            this._lastScanFingerprints = null;
            this._scanInProgress = false;
            console.log('[SYNC] Periodic sync stopped');
        }
        if (this._immediateSyncTimer) {
            clearTimeout(this._immediateSyncTimer);
            this._immediateSyncTimer = null;
        }
        if (this._peerReportDebounce) {
            clearTimeout(this._peerReportDebounce);
            this._peerReportDebounce = null;
        }
        this._stopFSObserver();
    },

    // Phase 1 (B): Immediate sync trigger after a local file_op.
    // Debounced (300ms) so rapid operations coalesce into a single push.
    // - deleteFile: local FS changed → run a full _doPeriodicScan (which detects
    //   the deletion and pushes fresh state to the other side).
    // - createFolder/renameFile/moveFile: local FS NOT changed (DB+fileCache only)
    //   → a scan would revert fileCache to stale local FS state, so the host
    //   pushes its in-memory fileCache to peers directly via _pushFileCacheToPeers.
    _triggerImmediateSync(reason) {
        if (!this.currentDrive) return;
        var self = this;
        if (this._immediateSyncTimer) clearTimeout(this._immediateSyncTimer);
        this._immediateSyncTimer = setTimeout(function() {
            self._immediateSyncTimer = null;
            self._doImmediateSync(reason);
        }, 300);
    },

    async _doImmediateSync(reason) {
        if (!this.currentDrive) return;
        // When using FileSystemObserver, the safety-net interval stays fixed
        // at 120s. Only reset to min for polling mode.
        if (!this._fsObserverSupported) {
            this._syncInterval = this._syncMinInterval;
            this._syncNoChangeCount = 0;
        }

        if (reason === 'delete' || reason === 'fs_event' || reason === 'rename' || reason === 'move') {
            // Local FS changed (delete/rename/move, or external change picked up by
            // FileSystemObserver): a real scan will detect the change and push.
            // If a scan is already running, the change will be caught by the
            // next periodic cycle (which is now reset to min interval).
            if (this._scanInProgress) {
                console.log('[SYNC] Immediate sync deferred (scan in progress), next cycle in ' + (this._syncInterval / 1000) + 's');
                return;
            }
            console.log('[SYNC] Immediate sync (' + reason + '): running scan now');
            await this._doPeriodicScan();
        } else {
            // mkdir: fileCache is authoritative, do NOT scan local FS.
            // Host pushes its current fileCache to all peers.
            if (this.isHost) {
                this._pushFileCacheToPeers();
            }
        }
    },

    // Host: push current in-memory fileCache to all peers via file_list_resp.
    // Used after mkdir where local FS does not reflect the change.
    _pushFileCacheToPeers() {
        if (!this.currentDrive || !this.isHost) return;
        var files = Array.from(this.fileCache.values());
        console.log('[SYNC] Immediate push: file_list_resp to all peers (' + files.length + ' files at ' + this.currentPath + ')');
        this.sendToAllPeers('file_list_resp', { files: files, path: this.currentPath });
    },

    // Phase 2 (A): FileSystemObserver integration for native file-change events.
    // On Chrome 129+ this delivers sub-second change notifications, replacing
    // the 1-60s polling loop as the primary change-detection mechanism. The
    // periodic scan remains as a fallback for unsupported browsers and as a
    // safety net. Start is idempotent; calling it again on a new folder first
    // stops the previous observer.
    _startFSObserver() {
        if (!this._fsObserverSupported) return;
        if (!this._boundFolder || !this._boundFolder.handle) return;
        if (this._fsObserver) return; // already observing this folder
        var self = this;
        try {
            this._fsObserver = new FileSystemObserver(function(records) {
                self._handleFSEvent(records);
            });
            this._fsObserver.observe(this._boundFolder.handle, { recursive: true });
            console.log('[SYNC] FileSystemObserver started on: ' + this._boundFolder.name + ' (recursive)');
        } catch (e) {
            console.warn('[SYNC] FileSystemObserver start failed, falling back to polling:', e);
            this._fsObserver = null;
        }
    },

    _stopFSObserver() {
        if (this._fsObserver) {
            try { this._fsObserver.disconnect(); } catch (e) {}
            this._fsObserver = null;
            console.log('[SYNC] FileSystemObserver stopped');
        }
    },

    // Called by FileSystemObserver on any file/folder change in the bound folder.
    // Events inside .tmpsync (sync state dir, never propagated) are ignored.
    // Bursts are coalesced by the 300ms debounce in _triggerImmediateSync.
    _handleFSEvent(records) {
        var hasExternalChange = false;
        for (var i = 0; i < records.length; i++) {
            var r = records[i];
            var path = r.relativePathComponents || [];
            if (path.length > 0 && path[0] === '.tmpsync') continue;
            // Skip ignored entries (system files, temp files, macOS metadata, etc.)
            var skip = false;
            for (var pi = 0; pi < path.length; pi++) {
                if (this._isIgnoredEntry(path[pi], false)) { skip = true; break; }
            }
            if (skip) continue;
            hasExternalChange = true;
            break;
        }
        if (!hasExternalChange) return;
        console.log('[SYNC] FileSystemObserver event: ' + records.length + ' record(s), triggering immediate sync');
        this._triggerImmediateSync('fs_event');
    },

    // Phase 3 (C): When the peer receives a push from the host (file_list_resp
    // or sync_delta), immediately re-report its local state so the host can
    // compute a fresh delta without waiting for the next periodic scan. Debounced
    // (500ms) to coalesce rapid arrivals. The transfer-busy guard in
    // sendPeerFileReport prevents re-reporting mid-transfer, and
    // handlePeerFileReport only sends a delta when there is actual work, so the
    // feedback loop terminates naturally once both sides are in sync.
    _schedulePeerReport() {
        if (this.isHost || !this.currentDrive) return;
        var self = this;
        if (this._peerReportDebounce) clearTimeout(this._peerReportDebounce);
        this._peerReportDebounce = setTimeout(function() {
            self._peerReportDebounce = null;
            // Reset periodic interval to min so subsequent local changes are picked up fast
            // (only for polling mode; FileSystemObserver mode uses fixed safety-net interval)
            if (!self._fsObserverSupported) {
                self._syncInterval = self._syncMinInterval;
                self._syncNoChangeCount = 0;
            }
            self.sendPeerFileReport();
        }, 500);
    },

    // Host: compare Peer's file report with Host's local files, send bidirectional delta.
    // Uses Dropbox-style sync rules with deletion propagation:
    //   - Key by file PATH (not fingerprint), so same path = same file slot
    //   - Same path + same size → in sync, skip
    //   - Same path + different size → conflict (newer mtime wins)
    //   - Only on Host + Peer never had it → Peer downloads (new file)
    //   - Only on Host + Peer deleted it → Host should also delete (propagate deletion)
    //   - Only on Peer + Host never had it → Peer uploads (new file)
    //   - Only on Peer + Host deleted it → Peer should also delete (propagate deletion)
    async handlePeerFileReport(peerFiles, peerDeleted, fromDevice, folderChanged) {
        if (!this.isHost) return;
        if (!this._boundFolder || !this._boundFolder.handle) {
            console.log('[SYNC] Host has no bound folder, skipping delta computation');
            return;
        }
        if (this._syncInProgress) {
            console.log('[SYNC] Sync already in progress, skipping this cycle');
            return;
        }
        this._syncInProgress = true;

        try {
            // Scan Host's local files
            var hostRawFiles = await this.getBoundFolderFiles();
            var hostFiles = [];
            var hostCurrentPaths = {};
            for (var i = 0; i < hostRawFiles.length; i++) {
                var f = hostRawFiles[i];
                if (f.is_dir) continue;
                var sha1 = await this._fingerprintFile(f.name, f.parent_path, f.size, f.mtime);
                var filePath = (f.parent_path === '/' ? '' : f.parent_path) + '/' + f.name;
                hostCurrentPaths[filePath] = true;
                hostFiles.push({
                    sha1: sha1,
                    name: f.name,
                    size: f.size,
                    mtime: f.mtime,
                    parent_path: f.parent_path || '/',
                    path: filePath
                });
            }

            // Build path-keyed maps
            var hostMap = {};
            for (var i = 0; i < hostFiles.length; i++) {
                hostMap[hostFiles[i].path] = hostFiles[i];
            }
            var peerMap = {};
            for (var j = 0; j < peerFiles.length; j++) {
                var pf = peerFiles[j];
                pf.path = (pf.parent_path === '/' ? '' : pf.parent_path) + '/' + pf.name;
                peerMap[pf.path] = pf;
            }

            // Build set of Peer paths that existed last sync.
            // When Peer just switched folders, Host must NOT propagate "missing
            // on Peer" as deletions to itself — the files are only missing
            // because Peer bound a fresh folder. Reset the record so Host's
            // files are treated as new files Peer should download instead.
            var peerHadPath = folderChanged ? {} : (this._peerLastPaths || {});
            // Build set of Host paths that existed last sync
            var hostHadPath = this._hostLastPaths || {};

            var download = [];      // Peer should download from Host
            var upload = [];        // Peer should upload to Host
            var conflict = [];      // Both modified, needs resolution
            var deleteOnPeer = [];  // Peer should delete these files (Host deleted them)
            var deleteOnHost = [];  // Host should delete these files (Peer deleted them)
            var inSync = 0;

            // 1. Process Peer-reported deletions: Host should delete these too.
            // Skip this entirely when Peer just switched folders — the
            // "deletions" are an artifact of the folder change, not real
            // deletions. Build the set for step 2 lookup regardless.
            var peerDeletedSet = {};
            if (!folderChanged) {
                (peerDeleted || []).forEach(function(delPath) {
                    peerDeletedSet[delPath] = true;
                    if (hostMap[delPath]) {
                        deleteOnHost.push(hostMap[delPath]);
                    }
                });
            }

            // 2. Collect all unique file paths from both sides
            var allPaths = {};
            for (var p in hostMap) allPaths[p] = true;
            for (var p in peerMap) allPaths[p] = true;

            for (var filePath in allPaths) {
                var hf = hostMap[filePath];
                var pf = peerMap[filePath];

                if (hf && !pf) {
                    // File is on Host but not on Peer
                    if (peerDeletedSet[filePath]) {
                        // Already handled via explicit peerDeleted in step 1 — skip
                        continue;
                    }
                    if (peerHadPath[filePath]) {
                        // Peer had this file before but not now → Peer deleted it
                        // Host should also delete (propagate deletion)
                        deleteOnHost.push(hf);
                    } else {
                        // Peer never had this file → new file, Peer should download
                        download.push(hf);
                    }
                } else if (!hf && pf) {
                    // File is on Peer but not on Host.
                    // Check Host's pending operations first — if Host deleted/renamed/moved
                    // this file, the operation takes precedence over Peer's state.
                    var pendingOp = self._hostPendingOps && self._hostPendingOps[filePath];
                    if (hostHadPath[filePath] || (pendingOp && pendingOp.op === 'delete')) {
                        // Host had/deleted this file → Peer should also delete
                        deleteOnPeer.push({ path: filePath, name: pf.name, parent_path: pf.parent_path, sha1: pf.sha1 });
                    } else if (pendingOp && (pendingOp.op === 'rename' || pendingOp.op === 'move')) {
                        // Host renamed/moved this file → Peer will get the update via sync_delta,
                        // don't treat the old path as a new file to upload
                        console.log('[SYNC] Skipping pending ' + pendingOp.op + ' path: ' + filePath);
                    } else {
                        // Host never had this file → new file, Peer should upload
                        upload.push(pf);
                    }
                } else if (hf && pf) {
                    // On both sides — compare by size
                    if (hf.size === pf.size) {
                        inSync++;
                    } else {
                        var hostTime = new Date(hf.mtime).getTime();
                        var peerTime = new Date(pf.mtime).getTime();
                        if (hostTime > peerTime) {
                            download.push(hf);
                        } else if (peerTime > hostTime) {
                            upload.push(pf);
                        } else {
                            conflict.push({
                                sha1: hf.sha1,
                                name: hf.name,
                                parent_path: hf.parent_path,
                                host_mtime: hf.mtime,
                                peer_mtime: pf.mtime,
                                host_size: hf.size,
                                peer_size: pf.size
                            });
                        }
                    }
                }
            }

            // Update last-known states for next cycle
            this._hostLastPaths = hostCurrentPaths;
            var peerCurrentPaths = {};
            for (var p in peerMap) peerCurrentPaths[p] = true;
            this._peerLastPaths = peerCurrentPaths;

            // Track Host-initiated deletions as pending — prevents race condition
            // where Peer reports the file still exists before completing the delete.
            if (!this._hostPendingOps) this._hostPendingOps = {};
            for (var di = 0; di < deleteOnPeer.length; di++) {
                var dp = deleteOnPeer[di];
                this._hostPendingOps[dp.path] = { op: 'delete', ts: Date.now() };
            }

            // Clean up resolved pending ops: paths no longer on either side
            for (var opPath in this._hostPendingOps) {
                var op = this._hostPendingOps[opPath];
                if (op.op === 'delete' && !peerMap[opPath] && !hostMap[opPath]) {
                    console.log('[SYNC] Host pending delete resolved: ' + opPath);
                    delete this._hostPendingOps[opPath];
                }
                if ((op.op === 'rename' || op.op === 'move') && !peerMap[opPath]) {
                    console.log('[SYNC] Host pending ' + op.op + ' resolved: ' + opPath);
                    delete this._hostPendingOps[opPath];
                }
            }

            // Execute Host-side deletions
            var peerSource = this._getDeviceDisplayName(fromDevice) || '';
            for (var i = 0; i < deleteOnHost.length; i++) {
                var dh = deleteOnHost[i];
                console.log('[SYNC] Propagating Peer deletion to Host: ' + dh.path);
                await this.handleRemoteDelete(dh.sha1, peerSource);
            }

            var totalWork = download.length + upload.length + conflict.length + deleteOnPeer.length + deleteOnHost.length;
            console.log('[SYNC] Dropbox delta: dl=' + download.length + ' ul=' + upload.length + ' conflict=' + conflict.length + ' delPeer=' + deleteOnPeer.length + ' delHost=' + deleteOnHost.length + ' inSync=' + inSync);

            // Only send delta if there's actual work to do
            if (totalWork === 0) {
                console.log('[SYNC] All files in sync, no transfer needed');
                return;
            }

            // Send delta to Peer via API
            this.sendToAllPeers('sync_delta', {
                download: download,
                upload: upload,
                conflict: conflict,
                delete_on_peer: deleteOnPeer
            });

            // Only log deletion activities — download/upload are internal sync
            // operations tracked by 'sync_received' and 'upload' activities on
            // the Peer side. Showing 'sync_push'/'sync_pull' here is misleading
            // because they fire on every delta cycle (including echo reports
            // where Peer re-reports files it just received from Host).
            if (deleteOnHost.length > 0) {
                this.addActivity('sync_delete', this._t('sync_act_host_delete').replace('{n}', deleteOnHost.length), { source: peerSource, target: this._t('sync_this_device') });
            }
            if (deleteOnPeer.length > 0) {
                this.addActivity('sync_delete', this._t('sync_act_notify_peer_delete').replace('{n}', deleteOnPeer.length), { source: this._t('sync_this_device'), target: this._t('sync_all_peers') });
            }
        } catch (e) {
            console.error('[SYNC] handlePeerFileReport failed:', e);
        } finally {
            this._syncInProgress = false;
            // Persist state to .tmpsync/state.json
            this._saveSyncState();
        }
    },
    
    // ========== WebRTC P2P Setup ==========
    // STUN server list: Google public STUN + self-hosted STUN.
    // The browser will automatically pick the fastest server.
    _DEFAULT_STUN_SERVERS: [
        { urls: 'stun:stun.l.google.com:19302' },
        { urls: 'stun:stun1.l.google.com:19302' },
        { urls: 'stun:sync.5t-cdn.com:3478' }
    ],

    async _fetchStunServers() {
        var cached = this._stunServersCache;
        if (cached && Date.now() < cached.expires) {
            return cached.iceServers;
        }
        try {
            var rsp = await fetch(
                'https://sync.5t-cdn.com:8981/api/stun/servers'
            );
            if (!rsp.ok) return this._DEFAULT_STUN_SERVERS;
            var data = await rsp.json();
            if (data.status !== 1 || !data.data || !data.data.iceServers) {
                return this._DEFAULT_STUN_SERVERS;
            }

            var servers = data.data.iceServers;
            console.log('[SYNC] STUN servers: ' + JSON.stringify(servers));

            this._stunServersCache = {
                iceServers: servers,
                expires: Date.now() + 3600 * 1000 // 1 hour cache
            };
            return servers;
        } catch (e) {
            console.warn('[SYNC] STUN servers fetch failed, using defaults:', e.message || e);
            return this._DEFAULT_STUN_SERVERS;
        }
    },

    _getIceServers() {
        var cached = this._stunServersCache;
        if (cached && Date.now() < cached.expires) {
            return cached.iceServers;
        }
        return this._DEFAULT_STUN_SERVERS;
    },

    async initWebRTC() {
        console.log('[SYNC] Initializing WebRTC, isHost=' + this.isHost);
        this._connState = 'connecting';
        var iceServers = await this._fetchStunServers();
        console.log('[SYNC] STUN servers: ' + (iceServers ? iceServers.length : 0) + ' configured');

        if (this.isHost) {
            // Host: per-peer architecture — no single RTCPeerConnection.
            // Each Peer gets its own PC created in _createOfferForPeer().
            // Just connect signaling; offers are created when peers come online.
            this.connectSignaling();
        } else {
            await this._createPeerConnection();
            this.connectSignaling();
        }
    },

    // _createPeerConnection creates a new RTCPeerConnection for the Peer
    // to connect to the Host. This method is reused by:
    // 1. initWebRTC() (initial connection)
    // 2. scheduleReconnect() (ICE renegotiation after failure)
    async _createPeerConnection() {
        var iceServers = await this._fetchStunServers();
        console.log('[SYNC] Creating new RTCPeerConnection (STUN servers: ' + (iceServers ? iceServers.length : 0) + ')');

        const config = {
            iceServers: iceServers,
            iceTransportPolicy: 'all'
        };
        this.rtcPeerConnection = new RTCPeerConnection(config);

        this.rtcPeerConnection.onicecandidate = (e) => {
            if (e.candidate) {
                var parts = (e.candidate.candidate || '').split(' ');
                var candType = parts.length > 7 ? parts[7] : 'unknown';
                console.log('[SYNC] ICE candidate gathered: type=' + candType + ' addr=' + (e.candidate.address || '?') + ' port=' + (e.candidate.port || '?'));
                this.sendSignaling({
                    type: 'ice_candidate',
                    candidate: e.candidate
                });
            } else {
                console.log('[SYNC] ICE gathering complete (null candidate)');
            }
        };

        this.rtcPeerConnection.onicegatheringstatechange = () => {
            console.log('[SYNC] ICE gathering state: ' + this.rtcPeerConnection.iceGatheringState);
        };

        this.rtcPeerConnection.oniceconnectionstatechange = () => {
            var state = this.rtcPeerConnection.iceConnectionState;
            console.log('[SYNC] ICE connection state: ' + state);

            if (state === 'connected' || state === 'completed') {
                if (this._iceTimeout) {
                    clearTimeout(this._iceTimeout);
                    this._iceTimeout = null;
                }
                // Detect connection mode (P2P vs Relay)
                this._detectConnectionMode(this.rtcPeerConnection, function(mode) {
                    if (VX_SYNC._hostConnectionMode !== mode) {
                        console.log('[SYNC] Host connection mode: ' + VX_SYNC._hostConnectionMode + ' -> ' + mode);
                        VX_SYNC._hostConnectionMode = mode;
                        VX_SYNC.updatePeerList();
                    }
                });
            }

            if (state === 'failed' || state === 'disconnected') {
                console.warn('[SYNC] ICE connection ' + state + ', will reconnect');
                if (this._iceTimeout) {
                    clearTimeout(this._iceTimeout);
                    this._iceTimeout = null;
                }
                this.scheduleReconnect();
            }
        };

        this.rtcPeerConnection.onconnectionstatechange = () => {
            var state = this.rtcPeerConnection.connectionState;
            console.log('[SYNC] Connection state: ' + state);

            if (state === 'failed') {
                console.warn('[SYNC] P2P connection failed, staying in relay mode');
                this._connState = 'failed';
                if (this._iceTimeout) {
                    clearTimeout(this._iceTimeout);
                    this._iceTimeout = null;
                }
                this._p2pFailCount = (this._p2pFailCount || 0) + 1;
                this._switchToRelayMode();
            } else if (state === 'connected') {
                this._p2pFailCount = 0;
                this._switchToP2PMode();
                var hostName = this._getHostDisplayName();
                var connLabel = '已直接连接到 ' + hostName;
                console.log('[SYNC] ' + connLabel + ' connection established');
                if (this._iceTimeout) {
                    clearTimeout(this._iceTimeout);
                    this._iceTimeout = null;
                }
                this.addActivity('p2p_connected', connLabel);
                this.updateStatus('ready');
            }
        };

        this.rtcPeerConnection.onicecandidateerror = (e) => {
            console.warn('[SYNC] ICE candidate error:', e.errorCode, e.errorText);
        };

        // Peer side: accept incoming DataChannel from Host
        this.rtcPeerConnection.ondatachannel = (e) => {
            console.log('[SYNC] Accepted incoming DataChannel: label=' + e.channel.label);
            this.acceptDC = e.channel;
            this.setupDataChannel(e.channel);
        };
    },

    // Detect whether the current ICE connection is P2P (direct via STUN).
    // No TURN relay, so the only possible candidate types are host, srflx, and prflx.
    _detectConnectionMode(pc, callback) {
        try {
            pc.getStats().then(function(report) {
                var candidateMap = {};
                report.forEach(function(s) {
                    if (s.type === 'local-candidate' || s.type === 'remote-candidate') {
                        candidateMap[s.id] = s.candidateType || '';
                    }
                });

                var mode = 'unknown';
                report.forEach(function(s) {
                    if (s.type === 'candidate-pair' && s.nominated) {
                        var localType = candidateMap[s.localCandidateId] || '';
                        var remoteType = candidateMap[s.remoteCandidateId] || '';
                        console.log('[SYNC] Active candidate pair: local=' + localType + ' remote=' + remoteType);
                        if (localType && remoteType) {
                            mode = 'p2p';
                        }
                    }
                });

                if (mode === 'unknown') {
                    mode = 'p2p'; // Default: if connected, it's P2P
                }
                callback(mode);
            }).catch(function(e) {
                callback('p2p');
            });
        } catch (e) {
            callback('p2p');
        }
    },

    // ========== Drive Entry (replaces old connectSignaling) ==========
    //
    // In the unified WSS architecture, we do NOT create a new WebSocket per drive.
    // Instead, we reuse the global per-user signalingWS and send a 'drive_enter'
    // message to register this device in the drive. The server responds with a
    // peer_list and broadcasts a 'presence' notification to other drive members.
    //
    // Host: per-peer architecture — each Peer gets its own RTCPeerConnection
    //       and DataChannel, created in _createOfferForPeer() when a Peer
    //       comes online (signaled by 'presence' → _handlePeerStatusNotification).
    // Peer: waits for the Host's webrtc_offer (triggered by the presence broadcast).
    async connectSignaling() {
        if (!this.signalingWS || this.signalingWS.readyState !== WebSocket.OPEN) {
            console.warn('[SYNC] signalingWS not open, cannot enter drive');
            this.scheduleReconnect();
            return;
        }

        console.log('[SYNC] Entering drive via WSS: drive=' + this.currentDrive.drive_id + ' isHost=' + this.isHost);
        this._connState = 'signaling';
        this._reconnectAttempt = 0;
        this.updateStatus('ready');
        this._startHeartbeat();

        // Send drive_enter to register device in drive state.
        // Server responds with drive_enter_resp + peer_list, and broadcasts presence.
        this.wsRequest('drive_enter', {
            drive_id: this.currentDrive.drive_id,
            device_id: this.getDeviceId(),
            device_name: this.deviceName || ''
        }, true);

        if (this.isHost) {
            // Host: per-peer architecture — DataChannels are created per-peer
            // in _createOfferForPeer(). Nothing to do here.
            console.log('[SYNC] Host connected to signaling, waiting for peers');
        }

        // Process any buffered signaling messages that arrived before
        // RTCPeerConnection was created (e.g., Host's webrtc_offer arrived
        // while the Peer was re-entering the drive after Host came online).
        if (this._pendingSignaling && this._pendingSignaling.length > 0) {
            var buffered = this._pendingSignaling;
            this._pendingSignaling = null;
            var self = this;
            console.log('[SYNC] Processing ' + buffered.length + ' buffered signaling message(s)');
            // Process asynchronously so connectSignaling's caller (initWebRTC)
            // can finish setting up event handlers first.
            setTimeout(function() {
                buffered.forEach(function(m) { self.handleSignalingMessage(m); });
            }, 0);
        }
    },
    
    scheduleReconnect() {
        // Host: per-peer architecture — no global reconnect. Individual peer
        // connections are managed via _closePeerConnection() and presence
        // notifications trigger new offers when peers come back online.
        if (this.isHost) {
            console.log('[SYNC] Host: skipping global reconnect (per-peer architecture)');
            return;
        }
        // Peer + host known offline: don't aggressively reconnect. We'll be
        // notified via peer_status (notification WS) when the host is back,
        // which triggers retryConnect() directly. This prevents burning the
        // reconnect budget while we're simply waiting for the host to return.
        if (!this.isHost && this.currentDrive && !this._hostOnline) {
            console.log('[SYNC] Host is offline, skipping reconnect (waiting for host)');
            return;
        }
        if (this._reconnectTimer) return;
        if (this._reconnectAttempt >= this._reconnectMax) {
            console.log('[SYNC] Max reconnect attempts reached');
            this.toastError(this._t('sync_connection_lost_refresh'));
            return;
        }
        // Don't reconnect if we're already connected or connecting
        if (this._connState === 'connected' || this._connState === 'connecting') {
            console.log('[SYNC] Skipping reconnect: state=' + this._connState);
            return;
        }

        var delay = Math.min(1000 * Math.pow(2, this._reconnectAttempt), 30000);
        this._reconnectAttempt++;

        console.log('[SYNC] Reconnecting in ' + delay + 'ms (attempt ' + this._reconnectAttempt + ')');
        this._connState = 'failed';

        this._reconnectTimer = setTimeout(async () => {
            this._reconnectTimer = null;
            // Guard: if WSS is not open, defer this attempt — the WSS
            // reconnect handler will trigger scheduleReconnect again.
            if (!this.signalingWS || this.signalingWS.readyState !== WebSocket.OPEN) {
                console.warn('[SYNC] WSS not ready, deferring reconnect');
                this._reconnectAttempt--;
                this.scheduleReconnect();
                return;
            }
            if (this.currentDrive) {
                // Close the old WebRTC connection. The WSS connection is still
                // alive, so we do NOT send drive_leave/drive_enter — that would
                // broadcast unnecessary presence offline/online notifications.
                // Instead, we rebuild the RTCPeerConnection and request the Host
                // to renegotiate via a dedicated webrtc_renegotiate message.
                if (this.rtcPeerConnection) {
                    try { this.rtcPeerConnection.close(); } catch (e) {}
                    this.rtcPeerConnection = null;
                }
                if (this.acceptDC) {
                    try { this.acceptDC.close(); } catch (e) {}
                    this.acceptDC = null;
                }
                this._offerInProgress = false;
                if (this._offerTimeout) { clearTimeout(this._offerTimeout); this._offerTimeout = null; }
                this._peerDeviceIds = {};

                this._connState = 'connecting';
                await this._createPeerConnection();
                this._requestWebRTCRenegotiate();
            }
        }, delay);
    },

    // _requestWebRTCRenegotiate sends a webrtc_renegotiate message to the Host
    // via WSS, requesting the Host to create a new SDP offer. This replaces the
    // old drive_leave/drive_enter pattern that caused unnecessary presence
    // offline/online broadcasts.
    _requestWebRTCRenegotiate() {
        if (!this.signalingWS || this.signalingWS.readyState !== WebSocket.OPEN) {
            console.warn('[SYNC] Cannot request renegotiate: WSS not open');
            return;
        }
        var driveId = this.currentDrive ? this.currentDrive.drive_id : '';
        var unified = {
            type: 'webrtc_renegotiate',
            drive_id: driveId,
            to_device: 'host',
            from_device: 'peer_' + this.getDeviceId()
        };
        this.signalingWS.send(JSON.stringify(unified));
        console.log('[SYNC] Requested WebRTC renegotiation from Host (drive=' + driveId + ')');
    },

    // _handleWebRTCRenegotiate (Host-side) handles a Peer's request to re-create
    // an SDP offer. Closes the existing per-peer connection if any and creates
    // a new offer via _createOfferForPeer.
    _handleWebRTCRenegotiate(msg) {
        if (!this.isHost) return;
        var peerDeviceId = this._extractDeviceIdFromPersistentId(msg.from_device);
        if (!peerDeviceId) {
            console.warn('[SYNC] webrtc_renegotiate: cannot extract device ID from ' + msg.from_device);
            return;
        }
        console.log('[SYNC] Peer ' + peerDeviceId + ' requested WebRTC renegotiation');

        // Close existing connection for this peer if any
        if (this._peerConnections[peerDeviceId]) {
            try { this._peerConnections[peerDeviceId].pc.close(); } catch (e) {}
            delete this._peerConnections[peerDeviceId];
        }

        // Create new SDP offer for this peer
        this._createOfferForPeer(peerDeviceId, '');
    },

    // ========== WebRTC Signaling Handler ==========
    //
    // Handles ONLY WebRTC signaling messages (webrtc_offer, webrtc_answer,
    // ice_candidate) received via the unified WSS connection.
    // All other message types are dispatched by _handleWSSMessage().
    handleSignalingMessage(msg) {
        // Peer side: buffer signaling messages if RTCPeerConnection is not ready yet.
        if (!this.isHost && !this.rtcPeerConnection &&
            (msg.type === 'webrtc_offer' || msg.type === 'ice_candidate')) {
            console.log('[SYNC] RTCPeerConnection not ready, buffering ' + msg.type);
            if (!this._pendingSignaling) this._pendingSignaling = [];
            this._pendingSignaling.push(msg);
            return;
        }

        // Peer side: guard against stale SDP messages
        if (!this.isHost && (msg.type === 'webrtc_offer' || msg.type === 'webrtc_answer')) {
            if (this._connState === 'connected') {
                console.log('[SYNC] Ignoring stale ' + msg.type + ': connection already established');
                return;
            }
            if (this._connState === 'disconnected' || this._connState === 'failed') {
                console.log('[SYNC] Ignoring ' + msg.type + ': connection is ' + this._connState + ', will reconnect');
                return;
            }
        }

        switch (msg.type) {
            case 'webrtc_offer':
                // Peer: Host sent an SDP offer, create answer
                console.log('[SYNC] Received webrtc_offer, creating answer');
                var pcState = this.rtcPeerConnection.signalingState;
                console.log('[SYNC] PeerConnection signaling state before setRemote: ' + pcState);
                var setRemote = Promise.resolve();
                if (pcState === 'have-remote-offer' || pcState === 'have-local-offer') {
                    console.log('[SYNC] Rolling back stale state before accepting new offer');
                    setRemote = this.rtcPeerConnection.setLocalDescription({ type: 'rollback' });
                }
                setRemote
                    .then(() => this.rtcPeerConnection.setRemoteDescription(new RTCSessionDescription(msg.sdp)))
                    .then(() => this.rtcPeerConnection.createAnswer())
                    .then(answer => {
                        console.log('[SYNC] Created SDP answer');
                        return this.rtcPeerConnection.setLocalDescription(answer);
                    })
                    .then(() => {
                        console.log('[SYNC] Sending webrtc_answer, iceGatheringState=' + this.rtcPeerConnection.iceGatheringState + ' signalingState=' + this.rtcPeerConnection.signalingState);
                        this.sendSignaling({ type: 'answer', sdp: this.rtcPeerConnection.localDescription });
                        var self = this;
                        if (this._iceTimeout) clearTimeout(this._iceTimeout);
                        var iceTimeoutMs = 15000;
                        this._iceTimeout = setTimeout(function() {
                            var iceState = self.rtcPeerConnection ? self.rtcPeerConnection.iceConnectionState : 'gone';
                            if (iceState !== 'connected' && iceState !== 'completed') {
                                console.warn('[SYNC] ICE connection timeout (state=' + iceState + '), staying in relay mode');
                                self._iceTimeout = null;
                                self._switchToRelayMode();
                            }
                        }, iceTimeoutMs);
                    })
                    .catch(err => {
                        console.error('[SYNC] Offer/answer exchange failed:', err);
                        console.warn('[SYNC] Reconnecting after failed offer/answer exchange');
                        this.scheduleReconnect();
                    });
                break;

            case 'webrtc_answer':
                // Host: Peer sent an SDP answer — route to the correct per-peer PC
                this._handleAnswerForPeer(msg);
                break;

            case 'ice_candidate':
                if (msg.candidate) {
                    if (this.isHost) {
                        // Host: route ICE candidate to the correct per-peer PC
                        this._handleIceCandidateForPeer(msg);
                    } else {
                        // Peer: add to single PC
                        var rParts = (msg.candidate.candidate || '').split(' ');
                        var rType = rParts.length > 7 ? rParts[7] : 'unknown';
                        console.log('[SYNC] Adding remote ICE candidate: type=' + rType);
                        this.rtcPeerConnection.addIceCandidate(new RTCIceCandidate(msg.candidate));
                        if (this._iceTimeout) {
                            clearTimeout(this._iceTimeout);
                            var iceSelf = this;
                            var iceCandTimeoutMs = 15000;
                            this._iceTimeout = setTimeout(function() {
                                var iceState = iceSelf.rtcPeerConnection ? iceSelf.rtcPeerConnection.iceConnectionState : 'gone';
                                if (iceState !== 'connected' && iceState !== 'completed') {
                                    console.warn('[SYNC] ICE connection timeout (state=' + iceState + '), staying in relay mode');
                                    iceSelf._iceTimeout = null;
                                    iceSelf._switchToRelayMode();
                                }
                            }, iceCandTimeoutMs);
                        }
                    }
                }
                break;

            default:
                console.log('[SYNC] Unhandled signaling message type: ' + msg.type, msg);
        }
    },

    // Host: route webrtc_answer to the correct per-peer PC based on from_device
    _handleAnswerForPeer(msg) {
        var peerDeviceId = this._extractDeviceIdFromPersistentId(msg.from_device);
        if (!peerDeviceId) {
            console.warn('[SYNC] Cannot route webrtc_answer: missing from_device');
            return;
        }
        var conn = this._peerConnections[peerDeviceId];
        if (!conn) {
            console.warn('[SYNC] No per-peer connection for webrtc_answer from: ' + peerDeviceId);
            return;
        }
        console.log('[SYNC] Received webrtc_answer from Peer: ' + peerDeviceId);
        var pc = conn.pc;
        var self = this;
        pc.setRemoteDescription(new RTCSessionDescription(msg.sdp))
            .then(function() {
                console.log('[SYNC] Remote description set for peer ' + peerDeviceId + ', signalingState=' + pc.signalingState);
            })
            .catch(function(err) {
                console.error('[SYNC] Failed to set remote description for peer ' + peerDeviceId + ':', err);
                self._closePeerConnection(peerDeviceId);
            });
    },

    // Host: route ice_candidate to the correct per-peer PC based on from_device
    _handleIceCandidateForPeer(msg) {
        var peerDeviceId = this._extractDeviceIdFromPersistentId(msg.from_device);
        if (!peerDeviceId) {
            console.warn('[SYNC] Cannot route ice_candidate: missing from_device');
            return;
        }
        var conn = this._peerConnections[peerDeviceId];
        if (!conn) {
            console.warn('[SYNC] No per-peer connection for ice_candidate from: ' + peerDeviceId);
            return;
        }
        var pc = conn.pc;
        var rParts = (msg.candidate.candidate || '').split(' ');
        var rType = rParts.length > 7 ? rParts[7] : 'unknown';
        console.log('[SYNC] Adding remote ICE candidate for peer ' + peerDeviceId + ': type=' + rType);
        pc.addIceCandidate(new RTCIceCandidate(msg.candidate)).catch(function(err) {
            console.warn('[SYNC] addIceCandidate failed for peer ' + peerDeviceId + ':', err);
        });
    },

    // Extract device_id from persistent peer ID (e.g., "peer_dev_xxx" → "dev_xxx")
    _extractDeviceIdFromPersistentId(persistentId) {
        if (!persistentId) return null;
        if (persistentId.indexOf('peer_') === 0) return persistentId.substring(5);
        if (persistentId.indexOf('host_') === 0) return persistentId.substring(5);
        return persistentId;
    },

    // Host: create SDP offer for a Peer that just came online.
    // Replaces the old 'peer_joined' handler. Called from _handlePeerStatusNotification
    // when a Peer's presence=online is received.
    _createOfferForPeer(peerDeviceId, peerDisplayName) {
        if (!this.isHost) {
            console.warn('[SYNC] _createOfferForPeer: not Host');
            return;
        }

        // Skip if already connected or connecting to this Peer
        if (this._peerConnections[peerDeviceId]) {
            console.log('[SYNC] Already have connection for peer: ' + peerDeviceId + ', skipping');
            return;
        }

        var peerPersistentId = 'peer_' + peerDeviceId;
        var iceServers = this._getIceServers();
        var self = this;

        console.log('[SYNC] Host creating per-peer RTCPeerConnection for: ' + peerDeviceId + ' (STUN servers: ' + (iceServers ? iceServers.length : 0) + ')');

        var pc = new RTCPeerConnection({
            iceServers: iceServers,
            iceTransportPolicy: 'all'
        });

        // Store peer connection state
        self._peerConnections[peerDeviceId] = {
            pc: pc,
            dc: null,
            mode: 'unknown',
            iceState: 'new',
            persistentId: peerPersistentId,
            displayName: peerDisplayName || ''
        };

        // Also track in _peerDeviceIds for P2P message routing (WSS sync_control)
        if (!self._peerDeviceIds) self._peerDeviceIds = {};
        self._peerDeviceIds[peerDeviceId] = peerPersistentId;

        // Create DataChannel for this Peer
        var dc = pc.createDataChannel('sync_channel_' + peerDeviceId, { ordered: true });
        self._peerConnections[peerDeviceId].dc = dc;
        self.setupDataChannel(dc, peerDeviceId);

        // ICE candidate handler — send to this specific Peer
        pc.onicecandidate = function(e) {
            if (e.candidate) {
                var parts = (e.candidate.candidate || '').split(' ');
                var candType = parts.length > 7 ? parts[7] : 'unknown';
                console.log('[SYNC] ICE candidate for peer ' + peerDeviceId + ': type=' + candType);
                self.sendSignaling({
                    type: 'ice_candidate',
                    candidate: e.candidate,
                    to_device: peerPersistentId
                });
            }
        };

        pc.oniceconnectionstatechange = function() {
            var state = pc.iceConnectionState;
            console.log('[SYNC] ICE state for peer ' + peerDeviceId + ': ' + state);
            if (self._peerConnections[peerDeviceId]) {
                self._peerConnections[peerDeviceId].iceState = state;
            }

            if (state === 'connected' || state === 'completed') {
                // Detect connection mode (P2P vs Relay) for this peer
                self._detectConnectionMode(pc, function(mode) {
                    if (self._peerConnections[peerDeviceId]) {
                        if (self._peerConnections[peerDeviceId].mode !== mode) {
                            console.log('[SYNC] Peer ' + peerDeviceId + ' connection mode: ' + mode);
                            self._peerConnections[peerDeviceId].mode = mode;
                            self.updatePeerList();
                        }
                    }
                });
            }

            if (state === 'failed' || state === 'disconnected') {
                console.warn('[SYNC] ICE ' + state + ' for peer ' + peerDeviceId + ', closing connection');
                self._closePeerConnection(peerDeviceId);
            }
        };

        pc.onconnectionstatechange = function() {
            var state = pc.connectionState;
            console.log('[SYNC] Connection state for peer ' + peerDeviceId + ': ' + state);
            if (state === 'connected') {
                self._connState = 'connected';
                self.addActivity('p2p_connected', '\u5df2\u8fde\u63a5\u5230 ' + (peerDisplayName || peerDeviceId));
                self.updateStatus('ready');
            }
            if (state === 'failed') {
                self._closePeerConnection(peerDeviceId);
            }
        };

        // Create offer and send to this specific Peer
        pc.createOffer()
            .then(function(offer) { return pc.setLocalDescription(offer); })
            .then(function() {
                console.log('[SYNC] Host sending webrtc_offer to peer: ' + peerDeviceId);
                self.sendSignaling({
                    type: 'offer',
                    sdp: pc.localDescription,
                    to_device: peerPersistentId
                });
            })
            .catch(function(err) {
                console.error('[SYNC] Host failed to create offer for peer ' + peerDeviceId + ':', err);
                self._closePeerConnection(peerDeviceId);
            });
    },

    // Close and clean up a single per-peer connection (Host side)
    _closePeerConnection(peerDeviceId) {
        var conn = this._peerConnections[peerDeviceId];
        if (!conn) return;
        console.log('[SYNC] Closing per-peer connection for: ' + peerDeviceId);
        try { conn.pc.close(); } catch (e) {}
        if (conn.dc) { try { conn.dc.close(); } catch (e) {} }
        delete this._peerConnections[peerDeviceId];
        // Also clean up _peerDeviceIds
        if (this._peerDeviceIds) {
            delete this._peerDeviceIds[peerDeviceId];
        }
        this.updatePeerList();
    },
    
    // ========== WebRTC Signaling (via unified WSS) ==========
    //
    // All WebRTC signaling (offer/answer/ICE) is routed through the single
    // signalingWS using the unified message format:
    //   { type: "webrtc_offer"|"webrtc_answer"|"ice_candidate",
    //     drive_id, from_device, to_device, sdp?, candidate? }
    //
    // The server routes the message to the target device via routeToDevice().
    sendSignaling(msg) {
        if (!this.signalingWS || this.signalingWS.readyState !== WebSocket.OPEN) {
            console.warn('[SYNC] Cannot send signaling: WS not open, msg=' + msg.type);
            return;
        }

        // Map old internal types to unified WSS types
        var typeMap = {
            offer: 'webrtc_offer',
            answer: 'webrtc_answer',
            ice_candidate: 'ice_candidate'
        };
        var wssType = typeMap[msg.type] || msg.type;

        // 'join' is no longer needed — drive_enter + presence replaces it
        if (msg.type === 'join') return;

        // Heartbeat is sent as a top-level type
        if (msg.type === 'heartbeat') {
            this.signalingWS.send(JSON.stringify({ type: 'heartbeat', request_id: Date.now() }));
            return;
        }

        // Ignore non-WebRTC types (latency_pong, etc.) — not needed in unified WSS
        if (wssType !== 'webrtc_offer' && wssType !== 'webrtc_answer' && wssType !== 'ice_candidate') {
            console.warn('[SYNC] Ignoring unsupported signaling type: ' + msg.type);
            return;
        }

        var driveId = this.currentDrive ? this.currentDrive.drive_id : '';
        var unified = {
            type: wssType,
            drive_id: driveId
        };

        // Determine target device
        if (this.isHost) {
            // Host → Peer: use explicitly set to_device, or broadcast
            unified.to_device = msg.to_device || '*';
        } else {
            // Peer → Host
            unified.to_device = this._getHostPersistentId();
        }

        // Attach SDP or ICE candidate at top level (server convenience fields)
        if (msg.sdp) {
            unified.sdp = { type: msg.sdp.type, sdp: msg.sdp.sdp };
        } else if (msg.candidate) {
            unified.candidate = {
                candidate: msg.candidate.candidate,
                sdpMid: msg.candidate.sdpMid || '',
                sdpMLineIndex: msg.candidate.sdpMLineIndex || 0
            };
        }

        this.signalingWS.send(JSON.stringify(unified));
    },

    // Peer: retry sending 'join' if no SDP offer arrives from Host within 5s.
    // This handles races where Host's peer_joined message was dropped or Host's
    // signaling WS was momentarily disconnected during the initial join.
    _startJoinRetry() {
        this._clearJoinRetry();
        this._joinRetryCount = 0;
        this._scheduleJoinRetry();
    },

    _scheduleJoinRetry() {
        var self = this;
        this._joinRetryTimer = setTimeout(function() {
            self._joinRetryTimer = null;
            if (!self.signalingWS || self.signalingWS.readyState !== WebSocket.OPEN) return;
            // Already connected via WebRTC? No need to retry.
            if (self.rtcPeerConnection && self.rtcPeerConnection.connectionState === 'connected') return;
            // Already processing an offer? Don't retry — Host is working on it.
            if (self.rtcPeerConnection) {
                var ss = self.rtcPeerConnection.signalingState;
                if (ss === 'have-remote-offer' || ss === 'have-local-offer') {
                    console.log('[SYNC] Skipping join retry: offer exchange in progress (signalingState=' + ss + ')');
                    self._scheduleJoinRetry();
                    return;
                }
            }
            self._joinRetryCount++;
            if (self._joinRetryCount > 3) {
                console.warn('[SYNC] Join retry limit reached, waiting for ICE timeout or manual retry');
                return;
            }
            console.warn('[SYNC] No offer received from Host, re-sending join (attempt ' + self._joinRetryCount + ')');
            self.sendSignaling({ type: 'join' });
            self._scheduleJoinRetry();
        }, 5000);
    },

    _clearJoinRetry() {
        if (this._joinRetryTimer) {
            clearTimeout(this._joinRetryTimer);
            this._joinRetryTimer = null;
        }
        this._joinRetryCount = 0;
    },

    // Send periodic application-level heartbeats so the server can detect
    // stuck connections even when WS ping/pong succeeds.
    _startHeartbeat() {
        this._stopHeartbeat();
        var self = this;
        this._heartbeatTimer = setInterval(function() {
            if (self.signalingWS && self.signalingWS.readyState === WebSocket.OPEN) {
                self.sendSignaling({ type: 'heartbeat' });
            }
        }, 30000);
    },

    _stopHeartbeat() {
        if (this._heartbeatTimer) {
            clearInterval(this._heartbeatTimer);
            this._heartbeatTimer = null;
        }
    },
    
    // ========== DataChannel Setup ==========
    setupDataChannel(dc, peerDeviceId) {
        dc.binaryType = 'arraybuffer';
        
        dc.onopen = () => {
            console.log('[SYNC] DataChannel opened: label=' + dc.label + ' readyState=' + dc.readyState + ' peer=' + (peerDeviceId || 'host'));
            VX_SYNC._connState = 'connected';

            if (this._connectTimeout) { clearTimeout(this._connectTimeout); this._connectTimeout = null; }
            if (this._iceTimeout) { clearTimeout(this._iceTimeout); this._iceTimeout = null; }

            // Peer: update loading progress — DataChannel is open, now waiting for file list
            if (!this.isHost) {
                this.updateLoadingProgress('正在同步文件列表...', '直连通道已建立', 60);
                // 全局 toast：Peer 连接成功（覆盖重连场景，初次连接也提示）
                var driveName = (this.currentDrive && (this.currentDrive.name || this.currentDrive.drive_name)) || '';
                VX_SYNC.toastSuccess(VX_SYNC._t('sync_toast_connected_to_host').replace('{name}', driveName));
            }

            // Start DataChannel keepalive to prevent TURN TCP idle timeout.
            // NAT/firewalls typically reclaim idle TCP connections after 30-60s.
            // A 20s interval keeps the TURN relay path active during periods
            // with no file transfer activity.
            if (dc._keepaliveTimer) clearInterval(dc._keepaliveTimer);
            dc._keepaliveTimer = setInterval(function() {
                if (dc.readyState === 'open') {
                    try { dc.send(JSON.stringify({ t: '_keepalive', ts: Date.now() })); } catch (e) {}
                }
            }, 20000);

            if (this.isHost && peerDeviceId) {
                // Host: update the per-peer DC reference
                if (this._peerConnections[peerDeviceId]) {
                    this._peerConnections[peerDeviceId].dc = dc;
                }
                // Host: send file list to this specific Peer via WSS sync_control
                this._listDirectoryAt('/').then(function(files) {
                    console.log('[SYNC] Host sending file_list_resp to peer ' + peerDeviceId + ': ' + files.length + ' files at /');
                    VX_SYNC.sendP2PMessage('file_list_resp', 'peer_' + peerDeviceId, { files: files, path: '/' });
                }).catch(function(e) {
                    console.warn('[SYNC] Host failed to list root for peer:', e);
                    VX_SYNC.sendP2PMessage('file_list_resp', 'peer_' + peerDeviceId, { files: [], path: '/' });
                });
            } else if (!this.isHost) {
                // Peer: request root file list from Host
                console.log('[SYNC] Peer requesting file list from Host');
                this.sendP2PMessage('file_list_req', this._getHostPersistentId(), { path: '/' });
                this.sendPeerFileReport();
            }
            this.startPeriodicSync();
        };
        
        dc.onmessage = (e) => {
            if (typeof e.data === 'string') {
                var msg = JSON.parse(e.data);
                this.handleControlMessage(msg, peerDeviceId, dc);
            } else {
                this.handleFileChunk(new Uint8Array(e.data), dc);
            }
        };
        
        dc.onclose = () => {
            console.log('[SYNC] DataChannel closed: label=' + dc.label + ' peer=' + (peerDeviceId || 'host'));
            // Stop keepalive timer
            if (dc._keepaliveTimer) {
                clearInterval(dc._keepaliveTimer);
                dc._keepaliveTimer = null;
            }
            if (this.isHost && peerDeviceId) {
                // Host: only close if this DC is still the current one for this
                // peer. During reconnection (drive_leave + drive_enter), the old
                // DC's onclose fires asynchronously AFTER the new connection is
                // already established. Without this guard, the stale onclose
                // would look up _peerConnections[peerDeviceId] (which now points
                // to the NEW connection) and close it, killing in-progress
                // downloads.
                var conn = this._peerConnections[peerDeviceId];
                if (conn && conn.dc === dc) {
                    this._closePeerConnection(peerDeviceId);
                } else {
                    console.log('[SYNC] Ignoring stale DC onclose for peer: ' + peerDeviceId);
                }
            } else {
                // Peer: only stop sync if this is the currently active DC.
                // Same stale-closure issue as Host side.
                if (this.acceptDC === dc) {
                    this.stopPeriodicSync();
                }
            }
        };

        dc.onerror = (e) => {
            console.error('[SYNC] DataChannel error: label=' + dc.label, e.message || e);
        };
        
        if (this.isHost) {
            this.dataChannel = dc; // Keep for backward compat (last opened DC)
        } else {
            this.acceptDC = dc;
        }
    },
    
    sendToDC(data, dc) {
        if (this.isHost) {
            // Host: if a specific dc is provided, use it; otherwise broadcast to all peer DCs
            if (dc) {
                if (dc.readyState === 'open') {
                    dc.send(typeof data === 'string' ? data : JSON.stringify(data));
                }
            } else {
                // Broadcast to all connected peer DCs
                var self = this;
                Object.keys(this._peerConnections).forEach(function(pid) {
                    var pdc = self._peerConnections[pid].dc;
                    if (pdc && pdc.readyState === 'open') {
                        pdc.send(typeof data === 'string' ? data : JSON.stringify(data));
                    }
                });
            }
        } else {
            // Peer: use acceptDC (or provided dc)
            var peerDC = dc || this.acceptDC;
            if (peerDC && peerDC.readyState === 'open') {
                peerDC.send(typeof data === 'string' ? data : JSON.stringify(data));
            } else {
                console.warn('[SYNC] Cannot send to DC: state=' + (peerDC ? peerDC.readyState : 'null'));
            }
        }
    },
    
    // ========== File Chunk Transfer (DataChannel only) ==========
    //
    // handleControlMessage processes ONLY file chunk transfer messages received
    // via the WebRTC DataChannel. All other control messages (file_list_req/resp,
    // peer_file_report, sync_delta, file_op) are handled by handleP2PMessage()
    // via the unified WSS connection.
    handleControlMessage(msg, peerDeviceId, dc) {
        // Silently drop keepalive messages — they only exist to keep the
        // TURN TCP connection alive through NAT/firewall idle timeouts.
        if (msg.t === '_keepalive') return;

        switch (msg.t) {
            case 'file_upload_start':
                this._downloads.set(msg.d.sha1, {
                    chunks: [],
                    meta: msg.d,
                    chunkSize: 0,
                    dc: dc,
                    peerDeviceId: peerDeviceId
                });
                this._currentTransferSha1 = msg.d.sha1;
                this._fileStatus.set(msg.d.sha1, 'downloading');
                this.showProgress(msg.d.name || msg.d.sha1, 0, msg.d.size);
                this._transferStartTime = Date.now();
                this._transferLastBytes = 0;
                this._transferLastTime = Date.now();
                this._transferSpeed = 0;
                var sourceNode = '';
                var mode = this._hostConnectionMode || 'unknown';
                if (this.isHost) {
                    sourceNode = (this._peerConnections[peerDeviceId] && this._peerConnections[peerDeviceId].displayName) || peerDeviceId || '';
                    mode = (this._peerConnections[peerDeviceId] && this._peerConnections[peerDeviceId].mode) || 'unknown';
                } else {
                    sourceNode = '\u4e3b\u673a';
                }
                this.upsertTransferActivity('download', msg.d.name || msg.d.sha1, msg.d.sha1, 0, '', mode, sourceNode);
                console.log('[SYNC] Starting download: ' + (msg.d.name || msg.d.sha1) + ' size=' + msg.d.size);
                break;

            case 'file_upload_done':
                var dlSha1 = msg.d.sha1;
                var download = this._downloads.get(dlSha1);
                if (download && download.chunks.length > 0) {
                    var chunkCount = download.chunks.length;
                    const blob = new Blob(download.chunks);
                    var dlSize = blob.size;
                    var dlMeta = download.meta || msg.d;
                    var dlName = dlMeta.name || dlSha1;
                    var dlSelf = this;

                    if (dlMeta.sync && this._boundFolder && this._boundFolder.handle) {
                        var writeMeta = dlMeta;
                        if (!writeMeta.parent_path) writeMeta.parent_path = '/';
                        this._writeFileToLocalFolder(writeMeta, blob).then(function(ok) {
                            if (ok) {
                                console.log('[SYNC] Sync file written to local folder: ' + dlName);
                            }
                            if (dlSelf._pendingDownloads) {
                                dlSelf._pendingDownloads.delete(dlSha1);
                                console.log('[SYNC] Pending downloads remaining: ' + dlSelf._pendingDownloads.size);
                                if (dlSelf._pendingDownloads.size === 0) {
                                    console.log('[SYNC] All pending downloads complete, scheduling re-report');
                                    if (dlSelf._pendingDownloadTimeout) {
                                        clearTimeout(dlSelf._pendingDownloadTimeout);
                                        dlSelf._pendingDownloadTimeout = null;
                                    }
                                    dlSelf._schedulePeerReport();
                                }
                            }
                        });
                    } else if (dlMeta.sync && this.isHost) {
                        this._triggerBrowserDownload(blob, dlName);
                        if (this._pendingDownloads) {
                            this._pendingDownloads.delete(dlSha1);
                            if (this._pendingDownloads.size === 0) {
                                this._schedulePeerReport();
                            }
                        }
                    } else {
                        this._triggerBrowserDownload(blob, dlName);
                        if (this._pendingDownloads) {
                            this._pendingDownloads.delete(dlSha1);
                            if (this._pendingDownloads.size === 0) {
                                this._schedulePeerReport();
                            }
                        }
                    }

                    this._transferStats.filesDownloaded++;
                    this._transferStats.bytesDownloaded += dlSize;
                    this._downloads.delete(dlSha1);
                    this.hideProgress();
                    this.updateTransferStats();
                    this._removeTransferActivity(dlSha1);
                    var dlSource = this.isHost
                        ? ((this._peerConnections[download.peerDeviceId] && this._peerConnections[download.peerDeviceId].displayName) || download.peerDeviceId || '')
                        : this._t('sync_role_host');
                    var dlMode = this.isHost
                        ? ((this._peerConnections[download.peerDeviceId] && this._peerConnections[download.peerDeviceId].mode) || 'unknown')
                        : (this._hostConnectionMode || 'unknown');
                    this.addActivity(dlMeta.sync ? 'sync_received' : 'download', dlName, { source: dlSource, target: this._t('sync_this_device'), mode: dlMode });
                    console.log('[SYNC] Download complete: ' + dlName + ' chunks=' + chunkCount + ' size=' + dlSize + ' sync=' + !!dlMeta.sync);
                }
                break;

            case 'file_download_req':
                // Host: Peer requested a file — enqueue with the requesting DC
                this._enqueueTransfer(msg.d.sha1, dc);
                break;

            default:
                console.log('[SYNC] Unhandled DC control message type: ' + msg.t, msg);
        }
    },
    
    handleFileChunk(data, dc) {
        var download = this._findDownloadByDC(dc);
        if (!download) return;
        download.chunks.push(new Uint8Array(data));
        download.chunkSize += data.byteLength || data.length;
        if (download.meta && download.meta.size) {
            this.updateProgress(download.chunkSize, download.meta.size);
        }
        if (download.chunks.length % 5 === 0) {
            var now = Date.now();
            var elapsed = (now - this._transferLastTime) / 1000;
            if (elapsed > 0.5) {
                var bytesDelta = download.chunkSize - this._transferLastBytes;
                this._transferSpeed = bytesDelta / elapsed;
                this._transferLastBytes = download.chunkSize;
                this._transferLastTime = now;
                var progress = download.meta && download.meta.size ? (download.chunkSize / download.meta.size * 100) : 0;
                var mode = this.isHost ? ((this._peerConnections[download.peerDeviceId] && this._peerConnections[download.peerDeviceId].mode) || 'unknown') : (this._hostConnectionMode || 'unknown');
                var sourceNode = this.isHost ? ((this._peerConnections[download.peerDeviceId] && this._peerConnections[download.peerDeviceId].displayName) || '') : '\u4e3b\u673a';
                this.upsertTransferActivity('download', download.meta.name || download.meta.sha1, download.meta.sha1, progress, this._formatSpeed(this._transferSpeed), mode, sourceNode);
            }
        }
        if (download.chunks.length % 20 === 0) {
            console.log('[SYNC] Received ' + download.chunks.length + ' chunks so far, ' + download.chunkSize + ' bytes');
        }
    },

    _findDownloadByDC(dc) {
        var result = null;
        this._downloads.forEach(function(d) {
            if (d.dc === dc) result = d;
        });
        return result;
    },
    
    async uploadFile(file) {
        if (!this._currentUserHasWritePermission()) {
            console.warn('[SYNC] uploadFile blocked: read-only permission');
            VXUI.showMsg(this._t('read_only_permission_denied'), 'error');
            return;
        }
        console.log('[SYNC] Uploading file: ' + file.name + ' size=' + file.size);
        const sha1 = await this.calculateSHA1(file);
        const metadata = {
            name: file.name,
            size: file.size,
            mtime: new Date(file.lastModified).toISOString(),
            ext: file.name.split('.').pop()
        };
        console.log('[SYNC] File SHA1 calculated: ' + sha1);

        this._currentTransferSha1 = sha1;
        this._fileStatus.set(sha1, 'uploading');
        this.showProgress(file.name, 0, file.size);
        // Init upload transfer tracking
        this._transferStartTime = Date.now();
        this._transferLastBytes = 0;
        this._transferLastTime = Date.now();
        this._transferSpeed = 0;
        var uploadMode = this.isHost ? 'local' : (this._hostConnectionMode || 'unknown');
        this.upsertTransferActivity('upload', file.name, sha1, 0, '', uploadMode, this.isHost ? '' : this._t('sync_role_host'));
        
        const CHUNK_SIZE = this.CHUNK_SIZE;
        var totalChunks = Math.ceil(file.size / CHUNK_SIZE);
        
        console.log('[SYNC] Uploading: ' + totalChunks + ' chunks');
        this.sendToDC({ t: 'file_upload_start', d: { ...metadata, sha1 } });
        
        let offset = 0;
        var chunkIndex = 0;
        const BUFFER_THRESHOLD = 4 * 1024 * 1024; // 4MB backpressure threshold
        var self = this;
        
        const sendChunk = async () => {
            if (offset >= file.size) {
                self.sendToDC({ t: 'file_upload_done', d: { sha1 } });
                self._transferStats.filesUploaded++;
                self._transferStats.bytesUploaded += file.size;
                self.hideProgress();
                self._removeTransferActivity(sha1);
                self.addActivity('upload', metadata.name, { source: self._t('sync_this_device'), target: self._t('sync_role_host'), mode: self._hostConnectionMode || 'unknown' });
                console.log('[SYNC] Upload complete: ' + file.name + ' size=' + file.size + ' chunks=' + chunkIndex);
                return;
            }
            
            const blob = file.slice(offset, offset + CHUNK_SIZE);
            const buffer = await blob.arrayBuffer();
            
            if (self.isHost) {
                // Host: broadcast file chunks to all connected peer DCs
                Object.keys(self._peerConnections).forEach(function(pid) {
                    var pdc = self._peerConnections[pid].dc;
                    if (pdc && pdc.readyState === 'open') {
                        pdc.send(buffer);
                    }
                });
                chunkIndex++;
            } else if (self.acceptDC) {
                // Event-based backpressure: wait for buffer to drain if needed
                var ok = await self._waitForBufferDrain(self.acceptDC, BUFFER_THRESHOLD);
                if (!ok) {
                    console.warn('[SYNC] DC closed during backpressure at chunk ' + (chunkIndex + 1));
                    self.hideProgress();
                    self._removeTransferActivity(sha1);
                    self.addActivity('upload', '\u53d1\u9001\u4e2d\u65ad: ' + metadata.name, { source: self._t('sync_this_device'), target: self._t('sync_role_host'), mode: self._hostConnectionMode || 'unknown' });
                    return;
                }
                self.acceptDC.send(buffer);
                chunkIndex++;
            }
            offset += CHUNK_SIZE;
            // Update upload progress every 5 chunks
            if (chunkIndex % 5 === 0) {
                var now = Date.now();
                var elapsed = (now - self._transferLastTime) / 1000;
                if (elapsed > 0.5) {
                    var bytesDelta = offset - self._transferLastBytes;
                    self._transferSpeed = bytesDelta / elapsed;
                    self._transferLastBytes = offset;
                    self._transferLastTime = now;
                    var progress = (offset / file.size * 100);
                    self.upsertTransferActivity('upload', file.name, sha1, progress, self._formatSpeed(self._transferSpeed), uploadMode, '');
                }
            }
            self.updateProgress(offset);
            // Yield to the event loop to allow DC to process
            setTimeout(sendChunk, 0);
        };
        
        sendChunk();
    },
    
    // Peer: upload a file from local folder to Host (bidirectional sync)
    async uploadFileToHost(sha1, meta) {
        if (this.isHost) return;
        if (!this._currentUserHasWritePermission()) {
            console.warn('[SYNC] uploadFileToHost blocked: read-only permission');
            return;
        }
        if (!this._boundFolder || !this._boundFolder.handle) {
            console.warn('[SYNC] uploadFileToHost: no bound folder');
            return;
        }

        try {
            // Locate file in Peer's local folder by parent_path + name
            var dirHandle = await this._getDirectoryHandle(meta.parent_path || '/');
            if (!dirHandle) {
                console.warn('[SYNC] uploadFileToHost: directory not found for ' + meta.parent_path);
                return;
            }
            var fileHandle = await dirHandle.getFileHandle(meta.name);
            var file = await fileHandle.getFile();
            console.log('[SYNC] uploadFileToHost: read local file ' + meta.name + ' size=' + file.size);

            // Send with sync flag so Host writes to its local folder
            var metadata = {
                name: file.name,
                size: file.size,
                mtime: new Date(file.lastModified).toISOString(),
                ext: file.name.split('.').pop(),
                sha1: sha1,
                parent_path: meta.parent_path || '/',
                sync: true
            };

            this._currentTransferSha1 = sha1;
            this._fileStatus.set(sha1, 'uploading');
            this.showProgress(file.name, 0, file.size);
            // Init upload transfer tracking
            this._transferStartTime = Date.now();
            this._transferLastBytes = 0;
            this._transferLastTime = Date.now();
            this._transferSpeed = 0;
            var upMode = this._hostConnectionMode || 'unknown';
            this.upsertTransferActivity('upload', file.name, sha1, 0, '', upMode, '\u4e3b\u673a');

            var CHUNK_SIZE = this.CHUNK_SIZE;
            var totalChunks = Math.ceil(file.size / CHUNK_SIZE);
            var BUFFER_THRESHOLD = 4 * 1024 * 1024; // 4MB backpressure threshold
            console.log('[SYNC] uploadFileToHost: ' + totalChunks + ' chunks');

            this.sendToDC({ t: 'file_upload_start', d: metadata });

            for (var i = 0; i < totalChunks; i++) {
                var start = i * CHUNK_SIZE;
                var end = Math.min(start + CHUNK_SIZE, file.size);
                var chunk = file.slice(start, end);
                var buffer = await chunk.arrayBuffer();

                var targetDC = this.acceptDC;
                if (!targetDC || targetDC.readyState !== 'open') {
                    console.warn('[SYNC] uploadFileToHost: DC closed at chunk ' + (i + 1) + '/' + totalChunks);
                    this.hideProgress();
                    this._removeTransferActivity(sha1);
                    return;
                }

                // Event-based backpressure: wait for buffer to drain if needed
                var ok = await this._waitForBufferDrain(targetDC, BUFFER_THRESHOLD);
                if (!ok) {
                    console.warn('[SYNC] uploadFileToHost: DC closed during backpressure at chunk ' + (i + 1));
                    this.hideProgress();
                    this._removeTransferActivity(sha1);
                    return;
                }

                targetDC.send(buffer);
                // Update progress every 5 chunks
                if ((i + 1) % 5 === 0 || i === totalChunks - 1) {
                    var now = Date.now();
                    var elapsed = (now - this._transferLastTime) / 1000;
                    if (elapsed > 0.5) {
                        var bytesDelta = end - this._transferLastBytes;
                        this._transferSpeed = bytesDelta / elapsed;
                        this._transferLastBytes = end;
                        this._transferLastTime = now;
                        var progress = (end / file.size * 100);
                        this.upsertTransferActivity('upload', file.name, sha1, progress, this._formatSpeed(this._transferSpeed), upMode, '\u4e3b\u673a');
                    }
                }
                this.updateProgress(end);
                if ((i + 1) % 10 === 0 || i === totalChunks - 1) {
                    console.log('[SYNC] uploadFileToHost: sent chunk ' + (i + 1) + '/' + totalChunks);
                }
            }

            // Wait for buffer to flush before signaling completion
            var dcDone = this.acceptDC;
            if (dcDone && dcDone.readyState === 'open') {
                await this._waitForBufferDrain(dcDone, 0);
            }

            this.sendToDC({ t: 'file_upload_done', d: { sha1: sha1, sync: true } });
            this._transferStats.filesUploaded++;
            this._transferStats.bytesUploaded += file.size;
            this.hideProgress();
            this._removeTransferActivity(sha1);
            this.addActivity('sync_upload', file.name, { source: this._t('sync_this_device'), target: this._t('sync_role_host'), mode: this._hostConnectionMode || 'unknown' });
            console.log('[SYNC] uploadFileToHost complete: ' + file.name + ' chunks=' + totalChunks);
        } catch (e) {
            console.warn('[SYNC] uploadFileToHost failed for ' + meta.name + ':', e);
            console.log('[SYNC] Retrying connection after upload failure');
            this.scheduleReconnect();
        }
    },
    
    async calculateSHA1(file) {
        const buffer = await file.arrayBuffer();
        const hashBuffer = await crypto.subtle.digest('SHA-1', buffer);
        const hashArray = Array.from(new Uint8Array(hashBuffer));
        return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
    },
    
    // ========== Sync Delta Processing ==========
    processDelta(delta, fromDevice) {
        var self = this;

        // Bidirectional delta format (from Host via P2P)
        if (delta.download || delta.upload || delta.conflict || delta.delete_on_peer) {
            var dlCount = (delta.download || []).length;
            var upCount = (delta.upload || []).length;
            var cfCount = (delta.conflict || []).length;
            var delCount = (delta.delete_on_peer || []).length;
            console.log('[SYNC] Processing bidirectional delta: download=' + dlCount + ' upload=' + upCount + ' conflict=' + cfCount + ' delete=' + delCount);

            // Download: Peer needs to fetch files from Host
            (delta.download || []).forEach(function(item) {
                var sha1 = item.sha1;
                // Skip if already downloading or pending — prevents duplicate
                // downloads when Host sends multiple sync_delta messages for the
                // same file before the Peer's updated peer_file_report arrives.
                if (self._pendingDownloads && self._pendingDownloads.has(sha1)) {
                    console.log('[SYNC] Skipping duplicate download: ' + sha1 + ' (already in progress)');
                    return;
                }
                console.log('[SYNC] Need to download from Host:', sha1, item.name);
                // Track as pending download — prevents stale peer_file_report
                // while files are being transferred and saved
                if (!self._pendingDownloads) self._pendingDownloads = new Set();
                self._pendingDownloads.add(sha1);
                // Update fileCache with Host's metadata
                self.fileCache.set(sha1, {
                    sha1: sha1,
                    name: item.name,
                    size: item.size,
                    mtime: item.mtime,
                    parent_path: item.parent_path,
                    status: 'synced'
                });
                self.sendToDC({ t: 'file_download_req', d: { sha1: sha1 } });
            });

            // Safety timeout: clear pending downloads after 120s in case
            // transfers fail silently (e.g. DataChannel drops mid-transfer).
            // Without this, stale entries would block peer_file_report forever.
            if (self._pendingDownloads && self._pendingDownloads.size > 0) {
                if (self._pendingDownloadTimeout) clearTimeout(self._pendingDownloadTimeout);
                self._pendingDownloadTimeout = setTimeout(function() {
                    if (self._pendingDownloads && self._pendingDownloads.size > 0) {
                        console.warn('[SYNC] Pending downloads timeout, clearing ' + self._pendingDownloads.size + ' stale entries');
                        self._pendingDownloads.clear();
                        
                        // Retry after transfer timeout
                        console.log('[SYNC] Retrying connection after transfer timeout');
                        self.scheduleReconnect();
                        
                        self._schedulePeerReport();
                    }
                    self._pendingDownloadTimeout = null;
                }, 120000);
            }

            // Upload: Peer should send these files to Host
            // Skip uploads for read-only peers — they cannot write to the host
            if (self._currentUserHasWritePermission()) {
                (delta.upload || []).forEach(function(item) {
                    var sha1 = item.sha1;
                    console.log('[SYNC] Need to upload to Host:', sha1);
                    self._enqueueUpload({ sha1: sha1, meta: item });
                });
            } else if ((delta.upload || []).length > 0) {
                console.warn('[SYNC] Skipping ' + delta.upload.length + ' upload(s) — read-only permission');
            }

            // Delete: Peer should delete these files (Host deleted them)
            (delta.delete_on_peer || []).forEach(function(item) {
                console.log('[SYNC] Deleting local file (Host deletion propagation):', item.path);
                var source = self._getDeviceDisplayName(fromDevice) || '主机';
                self.handleRemoteDelete(item.sha1, source);
            });

            // Conflict: both sides modified
            (delta.conflict || []).forEach(function(item) {
                console.log('[SYNC] Conflict detected:', item.sha1);
                self.pendingConflict = item;
                VXUI.openModal('sync-conflict-modal');
                var bodyEl = document.getElementById('sync-conflict-body');
                if (bodyEl) {
                    var lname = self.escapeHtml(item.name || item.sha1);
                    bodyEl.innerHTML = '<p>' + lname + '</p><p style="font-size:12px;color:var(--vx-text-secondary)">' + self._t('sync_local') + ': ' + item.peer_mtime + '<br>' + self._t('sync_role_host') + ': ' + item.host_mtime + '</p>';
                }
            });

            if (dlCount > 0 || upCount > 0 || delCount > 0) {
                self.addActivity('sync_delta', '\u4e0b\u8f7d ' + dlCount + ' / \u4e0a\u4f20 ' + upCount + ' / \u5220\u9664 ' + delCount + ' / \u51b2\u7a81 ' + cfCount, { source: self._t('sync_role_host'), target: self._t('sync_this_device') });
                // Re-render file list to show sync status
                self.renderFileList(Array.from(self.fileCache.values()));
            }
            return;
        }

        // Legacy delta format (from REST API: added/modified/deleted)
        var addedCount = (delta.added || []).length;
        var modifiedCount = (delta.modified || []).length;
        var deletedCount = (delta.deleted || []).length;
        console.log('[SYNC] Processing legacy delta: +' + addedCount + ' ~' + modifiedCount + ' -' + deletedCount);
        
        (delta.added || []).forEach(function(item) {
            var sha1 = typeof item === 'string' ? item : item.sha1;
            console.log('[SYNC] New file:', sha1);
            self.sendToDC({ t: 'file_download_req', d: { sha1: sha1 } });
        });
        
        (delta.modified || []).forEach(function(item) {
            var sha1 = typeof item === 'string' ? item : item.sha1;
            var remoteMtime = item.mtime;
            var local = self.fileCache.get(sha1);
            
            if (!local) {
                console.log('[SYNC] File modified remotely (new):', sha1);
                self.sendToDC({ t: 'file_download_req', d: { sha1: sha1 } });
                return;
            }
            
            var localTime = new Date(local.mtime).getTime();
            var remoteTime = new Date(remoteMtime).getTime();
            
            if (localTime < remoteTime) {
                console.log('[SYNC] File modified remotely:', sha1);
                self.sendToDC({ t: 'file_download_req', d: { sha1: sha1 } });
            } else if (localTime > remoteTime) {
                console.log('[SYNC] Conflict detected on:', sha1, '(local newer, marking conflict)');
                local.status = 'conflict';
                self.fileCache.set(sha1, local);
                self.pendingConflict = { sha1: sha1, name: local.name, localMtime: local.mtime, remoteMtime: remoteMtime };
                VXUI.openModal('sync-conflict-modal');
                var bodyEl = document.getElementById('sync-conflict-body');
                if (bodyEl) {
                    var lname = self.escapeHtml(local.name || sha1);
                    bodyEl.innerHTML = '<p>' + lname + '</p><p style="font-size:12px;color:var(--vx-text-secondary)">本地: ' + local.mtime + '<br>远程: ' + remoteMtime + '</p>';
                }
                self.renderFileList(Array.from(self.fileCache.values()));
            }
        });
        
        (delta.deleted || []).forEach(function(sha1) {
            console.log('[SYNC] File deleted remotely:', sha1);
            self.fileCache.delete(sha1);
        });
    },
    
    updateLocalCache(driveId, files) {
        // No-op: file list is always read from bound folder (Host) or via P2P (Peer)
        console.log('[SYNC] updateLocalCache skipped (no SQLite storage), drive=' + driveId + ' ' + (files ? files.length : 0) + ' files');
    },
    
    // ========== UI Rendering ==========
    render() {
        this.ensureLanguageReady().finally(() => {
            if (typeof TL !== 'undefined' && TL && typeof TL.tpl_lang === 'function') {
                setTimeout(() => TL.tpl_lang(), 0);
            }
        });
    },
    
    renderDriveList() {
        const container = document.getElementById('sync-drives');
        if (!container) return;

        var driveCount = this.drives.length;
        var driveLimit = this._getDriveLimit();
        // Disable create button when limit reached
        var createBtns = document.querySelectorAll('[onclick="VX_SYNC.showCreateDrive()"]');
        var limitReached = (driveCount >= driveLimit);
        createBtns.forEach(function(btn) {
            btn.disabled = limitReached;
            btn.style.opacity = limitReached ? '0.5' : '';
            btn.style.cursor = limitReached ? 'not-allowed' : '';
            btn.title = limitReached ? VX_SYNC._t('sync_drive_limit_reached').replace('{max}', driveLimit) : '';
        });

        // Don't show anything while loading
        if (!this._drivesLoaded) {
            container.innerHTML = '';
            return;
        }

        var pendingRequests = this._myPendingRequests || [];

        if (this.drives.length === 0 && pendingRequests.length === 0) {
            container.innerHTML = `
                <div style="display:flex;flex-direction:column;align-items:center;justify-content:center;padding:80px 20px;text-align:center;grid-column:1/-1">
                    <iconpark-icon name="link-cloud" size="48" style="color:var(--vx-text-muted);margin-bottom:16px"></iconpark-icon>
                    <p style="font-size:15px;color:var(--vx-text-secondary);margin:0" data-tpl="sync_no_drives_empty">\u6682\u65e0\u540c\u6b65\u76d8\uff0c\u8bf7\u5148\u521b\u5efa\u540c\u6b65\u76d8</p>
                </div>`;
            return;
        }

        var self = this;
        var pendingCardsHtml = pendingRequests.map(function(req) {
            return self._renderPendingRequestCard(req);
        }).join('');

        container.innerHTML = this.drives.map(drive => {
            var myDeviceId = this.getDeviceId();
            var isHost = (drive.host_device_id && drive.host_device_id === myDeviceId);
            var hostOnline = (drive.host_online === 1 || drive.host_online === true);
            var deleteLabel = isHost ? this._t('sync_delete_drive_title') : this._t('sync_delete_drive_leave');

            // 多 session 状态：本 tab 已运行 / 其它 tab 已占用 / 空闲
            var inThisTab = this.sessions.has(drive.drive_id);
            var lockedByOtherTab = !inThisTab && !!this._localDriveLocks[drive.drive_id];

            // Action button depending on role & lock state
            var actionHtml;
            var cardOnClick = 'VX_SYNC.enterDrive(\'' + drive.drive_id + '\')';
            if (lockedByOtherTab) {
                // 其它 tab 已占用：禁用按钮，卡片点击提示
                cardOnClick = 'VX_SYNC._showLockedByOtherTabHint(\'' + drive.drive_id + '\')';
                actionHtml = '<button class="vx-btn vx-btn-primary vx-btn-sm vx-sync-drive-action" disabled title="' + this._t('sync_running_in_other_tab') + '">' +
                    '<iconpark-icon name="lock"></iconpark-icon>' +
                    '<span>' + this._t('sync_running_in_other_tab') + '</span>' +
                    '</button>';
            } else if (inThisTab) {
                // 本 tab 已运行：按钮显示"进入"
                actionHtml = '<button class="vx-btn vx-btn-primary vx-btn-sm vx-sync-drive-action" onclick="VX_SYNC.enterDrive(\'' + drive.drive_id + '\'); event.stopPropagation();" title="' + this._t('sync_enter_session') + '">' +
                    '<iconpark-icon name="arrow-right"></iconpark-icon>' +
                    '<span>' + this._t('sync_enter_session') + '</span>' +
                    '</button>';
            } else if (isHost) {
                // Host: show "启动服务器" button (no online/offline status)
                actionHtml = '<button class="vx-btn vx-btn-primary vx-btn-sm vx-sync-drive-action" onclick="VX_SYNC.enterDrive(\'' + drive.drive_id + '\'); event.stopPropagation();" title="' + this._t('sync_start_server') + '">' +
                    '<iconpark-icon name="play"></iconpark-icon>' +
                    '<span>' + this._t('sync_start_server') + '</span>' +
                    '</button>';
            } else {
                // Peer: show connect button
                var connectDisabled = hostOnline ? '' : 'disabled';
                actionHtml = '<button class="vx-btn vx-btn-primary vx-btn-sm vx-sync-drive-action" ' + connectDisabled + ' onclick="VX_SYNC.enterDrive(\'' + drive.drive_id + '\'); event.stopPropagation();" title="' + this._t('sync_connect_host') + '">' +
                        '<iconpark-icon name="link"></iconpark-icon>' +
                        '<span>' + this._t('sync_connect_host') + '</span>' +
                    '</button>';
            }

            // Build role tag with online/offline status for Peer role
            var roleTagHtml;
            if (inThisTab) {
                // 本 tab 运行中：显示"运行中"标签
                roleTagHtml = '<span class="vx-sync-drive-tag vx-sync-drive-tag-running">' + this._t('sync_running_in_session') + '</span>';
            } else if (lockedByOtherTab) {
                roleTagHtml = '<span class="vx-sync-drive-tag vx-sync-drive-tag-locked">' + this._t('sync_running_in_other_tab') + '</span>';
            } else if (isHost) {
                roleTagHtml = '<span class="vx-sync-drive-tag vx-sync-drive-tag-host">' + this._t('sync_role_host') + '</span>';
            } else {
                var dotCls = 'vx-sync-host-dot ' + (hostOnline ? 'online' : 'offline');
                var statusLabel = hostOnline ? '\u5728\u7ebf' : '\u79bb\u7ebf';
                var statusTagCls = 'vx-sync-drive-status' + (hostOnline ? '' : ' vx-sync-drive-status-offline');
                roleTagHtml = '<span class="vx-sync-drive-tag vx-sync-drive-tag-peer">' + this._t('sync_role_peer') + '</span>' +
                    '<span class="' + statusTagCls + '"><span class="' + dotCls + '"></span>' + statusLabel + '</span>';
            }

            // Check if this is a shared drive (user is not the owner)
            var isShared = !isHost && String(drive.host_uid) !== String(TL.uid);
            var sharedTagHtml = isShared ? '<span class="vx-sync-drive-tag-shared">' + this._t('sync_shared') + '</span>' : '';

            var cardCls = 'vx-sync-drive-card';
            if (lockedByOtherTab) cardCls += ' vx-sync-drive-card-locked';

            return '<div class="' + cardCls + '" onclick="' + cardOnClick + '">' +
                '<button class="vx-sync-drive-delete-btn" onclick="VX_SYNC.promptDeleteDrive(\'' + drive.drive_id + '\', event)" title="' + deleteLabel + '">' +
                    '<iconpark-icon name="trash"></iconpark-icon>' +
                '</button>' +
                '<div class="vx-sync-drive-card-head">' +
                    '<div class="vx-sync-drive-icon">' +
                        '<iconpark-icon name="network-drive" size="28"></iconpark-icon>' +
                    '</div>' +
                    '<div class="vx-sync-drive-head-text">' +
                        '<h3>' + this.escapeHtml(drive.name || this._t('sync_drive_unnamed')) + ' ' + sharedTagHtml + '</h3>' +
                        '<div class="vx-sync-drive-meta">' +
                            '<span>' + (drive.peer_count || 0) + '/' + (drive.peer_limit || 10) + ' ' + this._t('sync_lobby_nodes') + '</span>' +
                            '<span class="vx-sync-drive-meta-sep">·</span>' +
                            '<span>' + this.formatDate(drive.created_at) + '</span>' +
                        '</div>' +
                    '</div>' +
                '</div>' +
                '<div class="vx-sync-drive-foot">' +
                    roleTagHtml +
                    '<div class="vx-sync-drive-action-area">' + actionHtml + '</div>' +
                '</div>' +
            '</div>';
        }).join('') + pendingCardsHtml;
    },

    // Render a pending-review card for one of the applicant's own join
    // requests. Card states: pending (审核中) / approved (可加入) / rejected (已拒绝).
    _renderPendingRequestCard(req) {
        var driveName = this.escapeHtml(req.drive_name || this._t('sync_drive_unnamed'));
        var created = this.formatDate(req.created_at);
        var status = req.status || 'pending';

        var statusBadgeHtml;
        var actionHtml;
        var cardCls = 'vx-sync-drive-card vx-sync-drive-card-pending';

        if (status === 'approved') {
            cardCls += ' vx-sync-drive-card-approved';
            statusBadgeHtml = '<span class="vx-sync-drive-tag vx-sync-drive-tag-approved">' + this._t('sync_join_status_approved') + '</span>';
            actionHtml = '<button class="vx-btn vx-btn-primary vx-btn-sm vx-sync-drive-action" onclick="VX_SYNC.joinApprovedDrive(\'' + req.drive_id + '\'); event.stopPropagation();" title="' + this._t('sync_join_now') + '">' +
                '<iconpark-icon name="link"></iconpark-icon>' +
                '<span>' + this._t('sync_join_now') + '</span>' +
                '</button>';
        } else if (status === 'rejected') {
            cardCls += ' vx-sync-drive-card-rejected';
            statusBadgeHtml = '<span class="vx-sync-drive-tag vx-sync-drive-tag-rejected">' + this._t('sync_join_status_rejected') + '</span>';
            actionHtml = '<button class="vx-btn vx-btn-ghost vx-btn-sm vx-sync-drive-action" onclick="VX_SYNC.dismissMyPendingRequest(\'' + req.drive_id + '\'); event.stopPropagation();" title="' + this._t('sync_dismiss') + '">' +
                '<span>' + this._t('sync_dismiss') + '</span>' +
                '</button>';
        } else {
            // pending
            statusBadgeHtml = '<span class="vx-sync-drive-tag vx-sync-drive-tag-pending">' + this._t('sync_join_status_pending') + '</span>';
            actionHtml = '<button class="vx-btn vx-btn-ghost vx-btn-sm vx-sync-drive-action" disabled title="' + this._t('sync_join_status_pending') + '">' +
                '<iconpark-icon name="time"></iconpark-icon>' +
                '<span>' + this._t('sync_join_status_pending') + '</span>' +
                '</button>';
        }

        var permLabel = req.permission === 'read_write' ? this._t('sync_permission_write') : this._t('sync_permission_read');
        var metaHtml = '<span>' + permLabel + '</span>' +
            '<span class="vx-sync-drive-meta-sep">·</span>' +
            '<span>' + created + '</span>';

        return '<div class="' + cardCls + '" onclick="VX_SYNC._pendingCardClick(\'' + req.drive_id + '\',\'' + status + '\')">' +
            '<div class="vx-sync-drive-card-head">' +
                '<div class="vx-sync-drive-icon">' +
                    '<iconpark-icon name="network-drive" size="28"></iconpark-icon>' +
                '</div>' +
                '<div class="vx-sync-drive-head-text">' +
                    '<h3>' + driveName + ' ' + statusBadgeHtml + '</h3>' +
                    '<div class="vx-sync-drive-meta">' + metaHtml + '</div>' +
                '</div>' +
            '</div>' +
            '<div class="vx-sync-drive-foot">' +
                '<span class="vx-sync-drive-pending-hint">' + this._t('sync_join_pending_hint') + '</span>' +
                '<div class="vx-sync-drive-action-area">' + actionHtml + '</div>' +
            '</div>' +
        '</div>';
    },

    // Click handler for pending cards: only approved cards enter the drive.
    _pendingCardClick(driveId, status) {
        if (status === 'approved') {
            this.joinApprovedDrive(driveId);
        }
    },

    // 卡片被其它 tab 占用时，点击提示用户
    _showLockedByOtherTabHint(driveId) {
        VXUI.showMsg(this._t('sync_drive_locked_other_tab_hint'), 'warn');
    },

    
    renderDetail() {
        document.getElementById('sync-drive-list').style.display = 'none';
        document.getElementById('sync-drive-detail').style.display = '';
        
        if (this.currentDrive) {
            document.getElementById('sync-drive-name').textContent = 
                this.currentDrive.drive_name || this.currentDrive.name || '同步盘';
        }
        
        this.currentPath = '/';
        this.listFiles();
    },

    renderFileList(files) {
        var listContainer = document.getElementById('sync-file-list');
        var listBody = document.getElementById('sync-file-tree');
        var emptyEl = document.getElementById('sync-empty-state');
        if (!listBody) return;

        // Merge local + remote files, computing per-file sync status
        var displayFiles = this._mergeFiles(files || []);

        if (displayFiles.length === 0) {
            if (listContainer) listContainer.style.display = 'none';
            if (emptyEl) emptyEl.style.display = 'flex';
            return;
        }
        if (listContainer) listContainer.style.display = '';
        if (emptyEl) emptyEl.style.display = 'none';

        listBody.innerHTML = displayFiles.map(f => {
            var sha1 = f.sha1;
            var name = this.escapeHtml(f.name);
            var isDir = f.is_dir == 1 || f.is_dir === true;
            var status = isDir ? 'synced' : (f._status || this._fileStatus.get(sha1) || 'synced');
            var statusHtml = this._renderStatusCell(sha1, status, f.mtime);

            if (isDir) {
                var safeName = f.name.replace(/'/g, "\\'");
                return '<div class="vx-list-row" data-sha1="' + sha1 + '" data-type="folder" ondblclick="VX_SYNC.openFolder(\'' + sha1 + '\',\'' + safeName + '\')" oncontextmenu="event.preventDefault();VX_SYNC.showContextMenu(\'' + sha1 + '\',\'' + name.replace(/'/g, "\\'") + '\',event.pageX,event.pageY)" style="cursor:pointer">' +
                    '<div class="vx-list-name">' +
                    '<div class="vx-list-icon"><iconpark-icon name="folder"></iconpark-icon></div>' +
                    '<div class="vx-list-filename"><a href="javascript:;" onclick="event.stopPropagation();VX_SYNC.openFolder(\'' + sha1 + '\',\'' + safeName + '\')">' + name + '</a></div>' +
                    '</div>' +
                    '<div class="vx-list-size">--</div>' +
                    '<div class="vx-list-mtime vx-hide-mobile">--</div>' +
                    statusHtml +
                    '</div>';
            }

            var size = this.formatFileSize(f.size);
            var icon = this.getFileIcon(f.name);
            var mtime = this.formatDateTime(f.mtime);
            return '<div class="vx-list-row" data-sha1="' + sha1 + '" data-type="file" ondblclick="VX_SYNC.downloadFile(\'' + sha1 + '\')" oncontextmenu="event.preventDefault();VX_SYNC.showContextMenu(\'' + sha1 + '\',\'' + name.replace(/'/g, "\\'") + '\',event.pageX,event.pageY)">' +
                '<div class="vx-list-name">' +
                '<div class="vx-list-icon"><iconpark-icon name="' + icon + '"></iconpark-icon></div>' +
                '<div class="vx-list-filename"><a href="javascript:;" onclick="event.stopPropagation();VX_SYNC.downloadFile(\'' + sha1 + '\')">' + name + '</a></div>' +
                '</div>' +
                '<div class="vx-list-size">' + size + '</div>' +
                '<div class="vx-list-mtime vx-hide-mobile">' + mtime + '</div>' +
                statusHtml +
                '</div>';
        }).join('');
    },

    // Merge remote files (from fileCache) with local files (from bound folder scan).
    // For Host: all files are local, just attach status.
    // For Peer: merge by full path, computing sync status.
    _mergeFiles(remoteFiles) {
        var self = this;
        if (this.isHost || !this._localFiles || this._localFiles.length === 0) {
            return (remoteFiles || []).map(function(f) {
                if (!f.is_dir) {
                    f._status = self._fileStatus.get(f.sha1) || 'synced';
                }
                return f;
            });
        }

        // Peer: merge local + remote by full path
        var remoteByPath = new Map();
        (remoteFiles || []).forEach(function(f) {
            remoteByPath.set(self._filePath(f), f);
        });

        var localByPath = new Map();
        this._localFiles.forEach(function(f) {
            localByPath.set(self._filePath(f), f);
        });

        var allPaths = new Set();
        remoteByPath.forEach(function(v, k) { allPaths.add(k); });
        localByPath.forEach(function(v, k) { allPaths.add(k); });

        var result = [];
        allPaths.forEach(function(path) {
            var remote = remoteByPath.get(path);
            var local = localByPath.get(path);

            if (remote && local) {
                if (remote.is_dir || local.is_dir) {
                    remote._status = 'synced';
                } else if (remote.size === local.size) {
                    remote._status = self._fileStatus.get(remote.sha1) || 'synced';
                } else {
                    remote._status = self._fileStatus.get(remote.sha1) || 'conflict';
                }
                result.push(remote);
            } else if (local) {
                local._status = self._fileStatus.get(local.sha1) || 'pending_upload';
                result.push(local);
            } else {
                remote._status = self._fileStatus.get(remote.sha1) || 'remote_only';
                result.push(remote);
            }
        });

        // Sort: folders first, then alphabetically
        result.sort(function(a, b) {
            var aIsDir = a.is_dir == 1 || a.is_dir === true;
            var bIsDir = b.is_dir == 1 || b.is_dir === true;
            if (aIsDir !== bIsDir) return bIsDir ? 1 : -1;
            return a.name.localeCompare(b.name);
        });

        return result;
    },

    // Build the full path of a file object
    _filePath(f) {
        if (!f.parent_path || f.parent_path === '/') return '/' + f.name;
        return f.parent_path + '/' + f.name;
    },

    // Render the status cell for a file row.
    // Shows sync status icon + text label.
    _renderStatusCell(sha1, status, mtime) {
        var cls = 'vx-text-muted';
        var icon = '';
        var text = '';

        switch (status) {
            case 'synced':
                icon = '<iconpark-icon name="circle-check" size="14" class="vx-sync-status-synced"></iconpark-icon>';
                text = '已同步';
                break;
            case 'pending_upload':
                icon = '<iconpark-icon name="cloud-arrow-up" size="14" class="vx-sync-status-pending"></iconpark-icon>';
                text = '待上传';
                cls = 'vx-text-warning';
                break;
            case 'remote_only':
                icon = '<iconpark-icon name="cloud" size="14" class="vx-sync-status-remote"></iconpark-icon>';
                text = '远程';
                break;
            case 'conflict':
                icon = '<iconpark-icon name="triangle-exclamation-solid" size="14" class="vx-sync-status-conflict"></iconpark-icon>';
                text = '冲突';
                cls = 'vx-text-danger';
                break;
            case 'uploading':
                icon = '<iconpark-icon name="cloud-arrow-up" size="14" class="vx-sync-status-pending"></iconpark-icon>';
                text = '上传中';
                cls = 'vx-text-warning';
                break;
            case 'downloading':
                icon = '<iconpark-icon name="cloud" size="14" class="vx-sync-status-remote"></iconpark-icon>';
                text = '下载中';
                break;
            case 'deleting':
                icon = '<iconpark-icon name="circle-xmark" size="14" class="vx-sync-status-remote"></iconpark-icon>';
                text = '删除中';
                cls = 'vx-text-danger';
                break;
        }

        return '<div class="vx-list-status">' +
            '<span class="' + cls + '">' + icon + text + '</span>' +
            '</div>';
    },

    // Update a single file row's status without re-rendering the entire list.
    _updateFileRow(sha1) {
        var row = document.querySelector('#sync-file-tree .vx-list-row[data-sha1="' + sha1 + '"]');
        if (!row) return;
        var status = this._fileStatus.get(sha1) || 'synced';
        var statusCol = row.querySelector('.vx-list-status');
        if (!statusCol) return;
        var mtime = '';
        var cached = this.fileCache.get(sha1);
        if (cached) mtime = cached.mtime;
        var statusHtml = this._renderStatusCell(sha1, status, mtime);
        // Replace the status column + any existing progress bar
        var existingProgress = row.querySelector('.vx-list-row-progress');
        if (existingProgress) existingProgress.remove();
        statusCol.outerHTML = statusHtml;
    },

    // Helper: translate a key via the app's i18n system
    _t(key) {
        if (typeof app !== 'undefined' && app && typeof app.languageData === 'object' && app.languageData[key]) {
            return app.languageData[key];
        }
        return key;
    },

    // Event-based backpressure wait: resolves when dc.bufferedAmount drops below threshold.
    // Much more efficient than polling with setTimeout.
    // Returns false if the DC closed during the wait.
    _waitForBufferDrain(dc, threshold) {
        if (!dc || dc.readyState !== 'open') return Promise.resolve(false);
        if (dc.bufferedAmount <= threshold) return Promise.resolve(true);

        // Use the bufferedamountlow event for efficient notification.
        // Set the threshold so the event fires when buffer drops below it.
        var prevThreshold = dc.bufferedAmountLowThreshold;
        dc.bufferedAmountLowThreshold = threshold;

        return new Promise(function(resolve) {
            var settled = false;
            var checkInterval = null;

            function done(ok) {
                if (settled) return;
                settled = true;
                dc.onbufferedamountlow = null;
                if (checkInterval) clearInterval(checkInterval);
                resolve(ok);
            }

            dc.onbufferedamountlow = function() {
                done(true);
            };

            // Safety-net: also poll every 50ms in case the event doesn't fire
            // (some browsers have quirks with bufferedamountlow).
            checkInterval = setInterval(function() {
                if (!dc || dc.readyState !== 'open') {
                    done(false);
                } else if (dc.bufferedAmount <= threshold) {
                    done(true);
                }
            }, 50);
        });
    },

    // Helper: parse a quota error from the server (e.g. "drive_limit_reached:1")
    // and return the corresponding localized message with {max} replaced.
    _quotaError(debug, prefix, i18nKey, fallbackKey) {
        if (debug && debug.indexOf(prefix + ':') === 0) {
            var max = debug.substring(prefix.length + 1);
            return this._t(i18nKey).replace('{max}', max);
        }
        return debug || this._t(fallbackKey);
    },

    // Check if the current user is a sponsor (drives higher quota limits).
    _isSponsor() {
        return typeof TL !== 'undefined' && TL.logined === 1 && TL.sponsor !== false;
    },

    // Max number of sync drives the current user can create.
    _getDriveLimit() {
        return this._isSponsor() ? 10 : 1;
    },

    // Max peer devices for the current drive (from server response, fallback to local check).
    _getPeerLimit() {
        if (this.currentDrive && this.currentDrive.peer_limit) {
            return this.currentDrive.peer_limit;
        }
        return this._isSponsor() ? 99 : 10;
    },

    // Format peer count with limit, e.g. "3/10".
    _formatPeerQuota(count) {
        var limit = this._getPeerLimit();
        return count + '/' + limit;
    },
    
    // ========== UI Actions ==========
    // Toggle the usage guide card. Collapse state persists in localStorage.
    toggleGuide() {
        this.trackUI('sync_toggle_guide');
        var guide = document.getElementById('sync-guide');
        if (!guide) return;
        var collapsed = guide.classList.toggle('vx-sync-guide-collapsed');
        try {
            localStorage.setItem('vx_sync_guide_collapsed', collapsed ? '1' : '0');
        } catch (e) {}
    },

    // Restore the guide collapse state from localStorage on module init.
    _restoreGuideState() {
        var guide = document.getElementById('sync-guide');
        if (!guide) return;
        var collapsed = '0';
        try {
            collapsed = localStorage.getItem('vx_sync_guide_collapsed') || '0';
        } catch (e) {}
        if (collapsed === '1') {
            guide.classList.add('vx-sync-guide-collapsed');
        }
    },

    showCreateDrive() {
        this.trackUI('sync_show_create');
        var nameInput = document.getElementById('sync-new-drive-name');
        if (nameInput) nameInput.value = '';
        VXUI.openModal('sync-create-modal');
    },
    
    hideCreateDrive() {
        VXUI.closeModal('sync-create-modal');
    },
    
    async doCreateDrive() {
        const name = document.getElementById('sync-new-drive-name').value.trim();
        this.hideCreateDrive();
        await this.createDrive(name);
    },

    // ========== Join Drive with Invite Code ==========

    showJoinDrive() {
        this.trackUI('sync_show_join');
        document.getElementById('sync-join-modal').style.display = 'flex';
        document.getElementById('sync-join-invite-code').value = '';
    },

    hideJoinDrive() {
        document.getElementById('sync-join-modal').style.display = 'none';
    },

    async doJoinDrive() {
        const inviteCode = document.getElementById('sync-join-invite-code').value.trim();
        if (!inviteCode) {
            VXUI.showMsg('请输入邀请码', 'error');
            return;
        }

        try {
            const resp = await this.wsRequest('join_request_apply', {
                invite_code: inviteCode,
                applicant_name: this.deviceName || this.deviceID,
            });
            if (resp.status !== 1) return;
            VXUI.showMsg(this._t('sync_join_request_submitted'), 'success');
            this.hideJoinDrive();

            // Immediately render a "审核中" card from the response data so
            // the applicant gets instant feedback without waiting for
            // loadMyJoinRequests to round-trip.
            var data = resp.data || {};
            var request = data.request || {};
            var drive = data.drive || {};
            var pendingItem = {
                id: request.id,
                drive_id: request.drive_id || drive.drive_id,
                drive_name: drive.drive_name || drive.name || '',
                host_uid: drive.host_uid,
                host_device_id: drive.host_device_id,
                host_online: drive.host_online,
                server_addr: drive.server_addr || '',
                permission: request.permission,
                status: request.status || 'pending',
                created_at: request.created_at || new Date().toISOString().replace('T', ' ').substring(0, 19)
            };
            // Avoid duplicates (re-applying for the same drive).
            this._myPendingRequests = this._myPendingRequests.filter(function(r) {
                return r.drive_id !== pendingItem.drive_id;
            });
            this._myPendingRequests.unshift(pendingItem);
            this.renderDriveList();

            // Re-fetch authoritative state in the background.
            this.loadMyJoinRequests();
        } catch (e) {
            console.error('join request failed', e);
            VXUI.showMsg('请求失败，请重试', 'error');
        }
    },

    // ========== Main Tab Switching ==========

    switchMainTab(tab) {
        this._mainTab = tab;
        this.trackUI('sync_main_tab_' + tab);

        document.querySelectorAll('.vx-sync-main-tab').forEach(function(btn) {
            btn.classList.toggle('active', btn.dataset.tab === tab);
        });
        document.getElementById('sync-main-view-drives').style.display = tab === 'drives' ? 'block' : 'none';
        document.getElementById('sync-main-view-messages').style.display = tab === 'messages' ? 'block' : 'none';

        if (tab === 'messages') {
            this.loadNotifications();
        }
    },

    _showMobileTopbar() {
        var topbar = document.getElementById('sync-mob-topbar');
        if (topbar) topbar.style.display = '';
        var titleEl = document.getElementById('sync-mob-title');
        if (titleEl && this.currentDrive) {
            var nameSpan = titleEl.querySelector('span');
            if (nameSpan) nameSpan.textContent = this.currentDrive.name || this.currentDrive.drive_name || '\u540c\u6b65\u76d8';
        }
    },

    _hideMobileTopbar() {
        var topbar = document.getElementById('sync-mob-topbar');
        if (topbar) topbar.style.display = 'none';
    },

    async enterDrive(driveId) {
        var drive = this.drives.find(function(r) { return r.drive_id === driveId; });
        if (!drive) {
            console.warn('[SYNC] enterDrive: drive not found id=' + driveId);
            return;
        }

        this.trackUI('sync_enter_drive');
        console.log('[SYNC] Entering drive: id=' + driveId + ' name=' + (drive.name || drive.drive_name || '(unnamed)') + ' host_device=' + (drive.host_device_id || 'none') + ' my_device=' + this.getDeviceId());

        // 若该 drive 已有 session，直接切换（多 session 并行场景）
        if (this.sessions.has(driveId)) {
            console.log('[SYNC] Session already exists for ' + driveId + ', switching');
            this.switchSession(driveId);
            return;
        }

        this.showLoading('正在加载同步盘信息...');

        // Determine Host by device_id: only the device that created the drive is Host.
        var myDeviceId = this.getDeviceId();
        var hostDeviceId = drive.host_device_id || '';
        var isHost = (hostDeviceId !== '' && hostDeviceId === myDeviceId);
        var role = isHost ? 'host' : 'peer';
        console.log('[SYNC] Role check: my_device=' + myDeviceId + ' host_device=' + hostDeviceId + ' → isHost=' + isHost);

        // 创建新 session 并设为活跃
        var session = this.createSession(drive, role);
        this.activeSessionId = driveId;

        // 同步镜像字段（旧代码通过 this.xxx 访问）
        this.currentDrive = drive;
        this.isHost = isHost;
        this._boundFolder = null;
        this.fileCache = session.fileCache;
        this.currentPath = '/';
        this.peers = session.peers;
        this._hostOnline = isHost ? true : (drive.host_online === 1 || drive.host_online === true);

        // 权限设置：所有者始终 read_write
        var isOwner = this._isDriveOwner(drive);
        if (isHost || isOwner) {
            session.permission = 'read_write';
            this._currentDrivePermission = 'read_write';
        } else {
            session.permission = drive.permission || null;
            this._currentDrivePermission = session.permission;
        }
        var permTab = document.getElementById('sync-tab-permissions');
        if (permTab) {
            permTab.style.display = (isHost || isOwner) ? 'flex' : 'none';
        }

        if (drive.server_addr) this.serverAddr = drive.server_addr;

        this.hideLoading();

        // Poll once via API to recover any messages that arrived before
        // the notification WS was connected (e.g., during reconnection).
        this.pollP2PMessages();

        // Peer: Host 离线时注册 presence 并显示 lobby
        if (!isHost && !this._hostOnline) {
            console.log('[SYNC] Host offline, registering for presence and showing lobby');
            if (this.signalingWS && this.signalingWS.readyState === WebSocket.OPEN) {
                this.wsRequest('drive_enter', {
                    drive_id: driveId,
                    device_id: myDeviceId,
                    device_name: this.deviceName || ''
                }, true);
            }
            this.showLobby();
            this._renderSessionSwitcher();
            return;
        }

        // Try to restore folder binding from IndexedDB
        var folderName = await this._restoreAndBindFolder(driveId);

        if (this._boundFolder && this._boundFolder.handle) {
            // Folder restored → 获取锁后连接
            console.log('[SYNC] Folder restored: ' + folderName + ', acquiring lock and connecting');
            session.boundFolder = this._boundFolder;
            var locked = await this._acquireFolderLock(session);
            if (!locked) {
                VXUI.showMsg(this._t('sync_folder_locked_other_tab'), 'warning');
                this._boundFolder = null;
                session.boundFolder = null;
                this.showLobby();
                this._renderSessionSwitcher();
                return;
            }
            this._bcast('drive_locked', {
                drive_id: driveId,
                role: role,
                folder_name: session.boundFolder.name
            });
            this._updateFolderPathDisplay();
            if (isHost) {
                this.startServer();
            } else {
                this.connectToHost();
            }
        } else {
            // No folder bound → 提示用户选择（selectFolder 中会获取锁）
            console.log('[SYNC] No folder binding, prompting user to select');
            this._updateFolderPathDisplay();
            if (isHost) {
                this.startServer();
            } else {
                this.connectToHost();
            }
        }
        this._renderSessionSwitcher();
    },

    showLobby() {
        if (!this.currentDrive) return;

        var drive = this.currentDrive;

        this._hideMobileTopbar();
        document.getElementById('sync-drive-list').style.display = 'none';
        document.getElementById('sync-drive-detail').style.display = 'none';
        document.getElementById('sync-drive-lobby').style.display = '';

        // Breadcrumb already shows drive name via sync-lobby-name in header
        var bcNameEl = document.querySelector('#sync-drive-lobby .vx-breadcrumb #sync-lobby-name');
        if (bcNameEl) bcNameEl.textContent = drive.name || drive.drive_name || '同步盘';

        var roleBadge = document.getElementById('sync-lobby-role');
        if (roleBadge) roleBadge.textContent = this.isHost ? this._t('sync_role_host') : this._t('sync_role_peer');

        this.updateRoleBadges();

        var dot = document.getElementById('sync-lobby-host-dot');
        if (dot) dot.className = this._hostOnline ? 'online' : 'offline';

        var hostText = document.getElementById('sync-lobby-host-text');
        if (hostText) hostText.textContent = this._hostOnline ? this._t('sync_status_online') : this._t('sync_status_offline');

        var nodesEl = document.getElementById('sync-lobby-nodes');
        if (nodesEl) nodesEl.textContent = this._formatPeerQuota(drive.peer_count || 0);

        this._updateFolderPathDisplay();

        var btnServer = document.getElementById('sync-lobby-btn-server');
        var btnConnect = document.getElementById('sync-lobby-btn-connect');
        var hintOffline = document.getElementById('sync-lobby-hint-offline');

        if (this.isHost) {
            if (btnServer) btnServer.style.display = '';
            if (btnConnect) btnConnect.style.display = 'none';
            if (hintOffline) hintOffline.style.display = 'none';
        } else {
            if (btnServer) btnServer.style.display = 'none';
            if (btnConnect) btnConnect.style.display = '';
            btnConnect.disabled = !this._hostOnline;
            if (hintOffline) hintOffline.style.display = this._hostOnline ? 'none' : '';
        }
    },

    async startServer() {
        if (!this.currentDrive || !this.isHost) return;
        this.trackUI('sync_start_server');

        // If no folder bound, prompt user to select one first
        if (!this._boundFolder || !this._boundFolder.handle) {
            try {
                await this.selectFolder();
                if (!this._boundFolder || !this._boundFolder.handle) {
                    // User cancelled folder selection
                    return;
                }
            } catch (e) {
                console.log('[SYNC] Folder selection cancelled or failed:', e);
                return;
            }
        }

        document.getElementById('sync-drive-list').style.display = 'none';
        document.getElementById('sync-drive-lobby').style.display = 'none';
        document.getElementById('sync-drive-detail').style.display = '';
        this._showMobileTopbar();
        this.switchDetailTab('files');

        this._hideHostOffline();
        this._setToolbarEnabled(true);
        this.updateStatus('ready');

        var nameEl = document.getElementById('sync-drive-name');
        if (nameEl) nameEl.textContent = this.currentDrive.name || this.currentDrive.drive_name || '同步盘';

        this.updateRoleBadges();

        this._updateFolderPathDisplay();
        this.render();
        this.renderActivityList();
        
        this.showLoading('正在扫描本地文件...', '读取文件夹内容', 10);
        this.currentPath = '/';
        // listFiles() scans the local FS and populates this._localFiles
        await this.listFiles();
        this.updateLoadingProgress('正在建立连接...', '初始化网络通道', 50);
        await this.initWebRTC();
        this.hideLoading();
        
        // Default to WSS relay mode; P2P probing runs in background
        this._switchToRelayMode();
        this._startP2PProbing();
        
        this.addActivity('start_server', (this.currentDrive.name || this.currentDrive.drive_name || '同步盘'));
    },

    async connectToHost() {
        if (!this.currentDrive || this.isHost) return;
        this.trackUI('sync_connect_host');
        if (!this._hostOnline) {
            this.toastWarning(this._t('sync_host_offline_cannot_connect'));
            return;
        }

        // Try to restore folder binding from previous session (like Host does)
        if (!this._boundFolder || !this._boundFolder.handle) {
            console.log('[SYNC] No folder bound, attempting to restore previous binding');
            var restoredName = await this._restoreAndBindFolder(this.currentDrive.drive_id);
            if (restoredName) {
                console.log('[SYNC] Folder binding restored: ' + restoredName);
            }
        }

        // If still no folder bound, prompt user to select one first
        if (!this._boundFolder || !this._boundFolder.handle) {
            try {
                await this.selectFolder();
                if (!this._boundFolder || !this._boundFolder.handle) {
                    return;
                }
            } catch (e) {
                console.log('[SYNC] Folder selection cancelled or failed:', e);
                return;
            }
        }

        document.getElementById('sync-drive-list').style.display = 'none';
        document.getElementById('sync-drive-lobby').style.display = 'none';
        document.getElementById('sync-drive-detail').style.display = '';
        this._showMobileTopbar();
        this.switchDetailTab('files');

        this._hideHostOffline();
        this._setToolbarEnabled(true);
        this.updateStatus('ready');

        var nameEl = document.getElementById('sync-drive-name');
        if (nameEl) nameEl.textContent = this.currentDrive.name || this.currentDrive.drive_name || '同步盘';

        this.updateRoleBadges();

        this._updateFolderPathDisplay();
        this.render();
        this.renderActivityList();
        
        this.currentPath = '/';
        this.showLoading('正在连接服务器...', '建立安全通道', 15);
        this.initWebRTC();

        // Default to WSS relay mode; P2P probing runs in background
        this._switchToRelayMode();
        this._startP2PProbing();

        // Safety timeout: if file_list_resp is not received within 30s, hide loading
        // and surface an error so the user isn't stuck staring at the mask.
        // 30s accounts for TURN relay ICE negotiation which can take 10-20s.
        // Cleared on DataChannel open (setupDataChannel) or file_list_resp received.
        if (this._connectTimeout) clearTimeout(this._connectTimeout);
        this._connectTimeout = setTimeout(function() {
            if (VX_SYNC._loadingCount > 0) {
                console.warn('[SYNC] Timed out waiting for file_list_resp from Host');
                VX_SYNC.hideLoading();
                VX_SYNC.toastError(VX_SYNC._t('sync_connect_host_timeout'));
            }
        }, 30000);

        this.addActivity('connect_host', (this.currentDrive.name || this.currentDrive.drive_name || '同步盘'));
    },

    _showHostOffline() {
        console.log('[SYNC] Host went offline, showing offline overlay');
        this._setToolbarEnabled(false);
        this.updateStatus('offline');
        var offlineEl = document.getElementById('sync-host-offline');
        if (offlineEl) offlineEl.style.display = '';
        var contentEl = document.getElementById('sync-content-area');
        if (contentEl) contentEl.style.display = 'none';
        var tabsEl = document.getElementById('sync-detail-tabs');
        if (tabsEl) tabsEl.style.display = 'none';
        var statusEl = document.getElementById('sync-status-bar');
        if (statusEl) statusEl.style.display = 'none';
    },

    _hideHostOffline() {
        var offlineEl = document.getElementById('sync-host-offline');
        if (offlineEl) offlineEl.style.display = 'none';
        var contentEl = document.getElementById('sync-content-area');
        if (contentEl) contentEl.style.display = '';
        var tabsEl = document.getElementById('sync-detail-tabs');
        if (tabsEl) tabsEl.style.display = '';
        var statusEl = document.getElementById('sync-status-bar');
        if (statusEl) statusEl.style.display = '';
    },

    switchDetailTab(tab) {
        this.trackUI('sync_tab_' + tab);
        this._detailTab = tab;
        var layout = document.getElementById('sync-detail-layout');
        if (layout) layout.setAttribute('data-active', tab);
        var tabs = document.querySelectorAll('.vx-sync-detail-tab');
        tabs.forEach(function(t) {
            t.classList.toggle('active', t.getAttribute('data-tab') === tab);
        });
        // Show only the active list view
        var views = ['files', 'permissions', 'peers', 'activity'];
        views.forEach(function(v) {
            var el = document.getElementById('sync-view-' + v);
            if (el) el.style.display = (v === tab) ? '' : 'none';
        });
        // Load permissions data when entering permissions tab
        if (tab === 'permissions') {
            this.loadInviteCodes();
            this.loadJoinRequests();
        }
    },

    // Update role badges (no longer shown in UI, kept for compatibility)
    updateRoleBadges() {
        // Role badges removed from UI - no-op
    },

    _setToolbarEnabled(enabled) {
    },

    _isHostAlive() {
        if (this.isHost) return true;
        if (!this._hostOnline) {
            this.toastWarning(this._t('sync_host_offline_unavailable'));
            return false;
        }
        return true;
    },

    async retryConnect() {
        if (!this.currentDrive) {
            console.warn('[SYNC] retryConnect: no current drive');
            return;
        }
        var drive = this.drives.find(function(r) { return r.drive_id === VX_SYNC.currentDrive.drive_id; });
        if (!drive) {
            console.warn('[SYNC] retryConnect: drive not found in list');
            return;
        }
        this._hostOnline = this.isHost ? true : (drive.host_online === 1 || drive.host_online === true);
        console.log('[SYNC] Retry connect: host_online=' + this._hostOnline);
        if (this._hostOnline) {
            this.showLoading('正在重试连接...');
            this._hideHostOffline();
            this._setToolbarEnabled(true);
            this.updateStatus('ready');
            // Clean up old connection before re-initializing
            this._cleanupConnection();
            if (this.isHost) {
                // Host: list files directly, then init WebRTC
                this.currentPath = '/';
                await this.listFiles();
                await this.initWebRTC();
                this.hideLoading();
                // Default to relay mode; P2P probing runs in background
                this._switchToRelayMode();
                this._startP2PProbing();
            } else {
                // Peer: init WebRTC, loading hidden when file_list_resp received
                await this.initWebRTC();
                // Default to relay mode; P2P probing runs in background
                this._switchToRelayMode();
                this._startP2PProbing();
            }
        } else {
            console.warn('[SYNC] Retry connect: host still offline');
            this.toastWarning(this._t('sync_host_still_offline'));
        }
    },

    // Handle peer_status notification: update drive list and current view
    // when a host or peer goes online/offline.
    _handlePeerStatusNotification(msg) {
        var driveId = msg.drive_id;
        var isOnline = msg.online;
        var role = msg.role; // 'host' or 'peer'
        var deviceName = msg.device_name || '';
        var shortId = msg.device_id ? String(msg.device_id).substring(0, 8) : '';
        var displayName = (deviceName && deviceName.length > 0) ? deviceName : ('设备 ' + shortId);

        // 1. Update the drive in the drives list
        for (var i = 0; i < this.drives.length; i++) {
            if (this.drives[i].drive_id === driveId) {
                if (role === 'host') {
                    this.drives[i].host_online = isOnline ? 1 : 0;
                } else {
                    // Update peer_count: +1 when online, -1 when offline
                    var count = this.drives[i].peer_count || 0;
                    if (isOnline) {
                        this.drives[i].peer_count = count + 1;
                    } else {
                        this.drives[i].peer_count = Math.max(0, count - 1);
                    }
                }
                break;
            }
        }

        // 2. If currently viewing this drive, update the UI
        if (this.currentDrive && this.currentDrive.drive_id === driveId) {
            if (role === 'host') {
                this._hostOnline = isOnline;
                // If we're a Peer and Host just came online, try to reconnect
                if (!this.isHost && isOnline) {
                    // Skip if already connected — no need to reconnect
                    if (this._connState === 'connected' && this.acceptDC && this.acceptDC.readyState === 'open') {
                        console.log('[SYNC] Host online but already connected, skipping reconnect');
                    } else {
                        console.log('[SYNC] Host came online, attempting reconnect');
                        // Reset reconnect state and retry immediately
                        this._reconnectAttempt = 0;
                        if (this._reconnectTimer) {
                            clearTimeout(this._reconnectTimer);
                            this._reconnectTimer = null;
                        }
                        // If we're in the lobby (peer opened drive while host was
                        // offline, never connected), re-enter the drive to restore
                        // folder binding and connect. retryConnect() assumes we're
                        // already in the detail view with a bound folder, so it
                        // doesn't work for the lobby case — it neither hides the
                        // lobby nor handles folder selection.
                        var lobbyEl = document.getElementById('sync-drive-lobby');
                        if (lobbyEl && lobbyEl.style.display !== 'none') {
                            console.log('[SYNC] In lobby, re-entering drive to connect');
                            this.enterDrive(this.currentDrive.drive_id);
                        } else {
                            this.retryConnect();
                        }
                    }
                    this.addActivity('host_online', displayName + ' 已上线');
                    this.toastSuccess(this._t('sync_toast_host_online').replace('{name}', displayName));
                }
                // If Host went offline and we're a Peer, immediately enter the
                // waiting-for-host state. The notification WS push delivers this
                // in real time (no need to wait for ICE/WS timeouts), which is
                // the real-time benefit WS brings to presence detection.
                if (!this.isHost && !isOnline) {
                    console.log('[SYNC] Host went offline via WS push, entering waiting state');
                    this._connState = 'disconnected';
                    this._stopP2PProbing();
                    this._connectionMode = 'wss_relay';
                    this._showHostOffline();
                    this.stopPeriodicSync();
                    // Close the old WebRTC connection so that when the Host comes
                    // back and sends a new offer, it gets buffered (rtcPeerConnection
                    // is null) instead of being discarded as "stale" by the
                    // _connState === 'connected' guard in handleSignalingMessage.
                    if (this.rtcPeerConnection) {
                        try { this.rtcPeerConnection.close(); } catch (e) {}
                        this.rtcPeerConnection = null;
                    }
                    if (this.acceptDC) {
                        try { this.acceptDC.close(); } catch (e) {}
                        this.acceptDC = null;
                    }
                    // Cancel any pending reconnect — we wait for the host to come
                    // back (signaled by a peer_status online notification, which
                    // triggers retryConnect directly) instead of burning reconnect
                    // attempts against a dead host.
                    if (this._reconnectTimer) {
                        clearTimeout(this._reconnectTimer);
                        this._reconnectTimer = null;
                    }
                    this._reconnectAttempt = 0;
                    this.addActivity('host_offline', displayName + ' 已离线');
                    this.toastWarning(this._t('sync_toast_host_offline').replace('{name}', displayName));
                }
            } else {
                // Peer online/offline — update node count display
                var nodesEl = document.getElementById('sync-peer-count');
                if (nodesEl) {
                    var d = this.drives.find(function(d) { return d.drive_id === driveId; });
                    if (d) nodesEl.textContent = String(d.peer_count || 0);
                }
                // Update this.peers array for dynamic peer list rendering
                if (msg.device_id) {
                    if (isOnline) {
                        // Add peer if not already in list
                        var exists = this.peers.some(function(p) { return p.device_id === msg.device_id; });
                        if (!exists) {
                            this.peers.push({
                                device_id: msg.device_id,
                                device_name: deviceName,
                                peer_id: msg.role === 'host' ? ('host_' + msg.device_id) : ('peer_' + msg.device_id),
                                role: msg.role || 'peer',
                                online: true
                            });
                        }
                    } else {
                        // Remove peer from list
                        this.peers = this.peers.filter(function(p) { return p.device_id !== msg.device_id; });
                    }
                }
                if (isOnline) {
                    this.addActivity('peer_join', displayName + ' 已加入');
                    this.toastInfo(this._t('sync_toast_peer_join').replace('{name}', displayName));
                    // Host: create SDP offer for the newly online Peer.
                    if (this.isHost && msg.device_id) {
                        console.log('[SYNC] Host detected peer online via presence: ' + msg.device_id);
                        this._createOfferForPeer(msg.device_id, displayName);
                    }
                } else {
                    this.addActivity('peer_leave', displayName + ' 已离开');
                    this.toastInfo(this._t('sync_toast_peer_leave').replace('{name}', displayName));
                    // Host: close the per-peer connection for this Peer
                    if (this.isHost && msg.device_id) {
                        console.log('[SYNC] Host closing connection for offline peer: ' + msg.device_id);
                        this._closePeerConnection(msg.device_id);
                    }
                }
            }

            // Update the status bar
            this.updateStatus();
            // Re-render peer list to show updated connection modes
            this.updatePeerList();
        }

        // 3. Re-render drive list
        this.renderDriveList();
    },

    // Handle drive_deleted notification from signaling server.
    // Called when the Host deletes the drive — all peers are disconnected
    // and the drive is automatically closed.
    _handleDriveDeleted(driveId) {
        console.log('[SYNC] _handleDriveDeleted: drive=' + driveId);
        // Stop reconnect attempts
        if (this._reconnectTimer) {
            clearTimeout(this._reconnectTimer);
            this._reconnectTimer = null;
        }
        this._reconnectAttempt = this._reconnectMax; // Prevent further reconnects

        // Cleanup connections (WebSocket, WebRTC, DataChannels)
        this._cleanupConnection();

        // Remove the deleted drive from local list
        this.drives = this.drives.filter(function(d) { return d.drive_id !== driveId; });

        // Remove stored folder handle
        this._removeStoredFolderHandle(driveId);

        // Clear .tmpsync state (drive is permanently deleted)
        this._clearSyncState();

        // Reset state
        this.currentDrive = null;
        this.isHost = false;
        this._hostOnline = true;
        this.fileCache.clear();
        this._localFiles = [];
        this._fileStatus.clear();
        this._fileProgress.clear();
        this._currentTransferSha1 = null;
        this._downloads.clear();
        this.peers = [];
        this._boundFolder = null;
        this._connectionMode = 'wss_relay';
        this._transferQueue = [];
        this._transferBusy = false;
        this._syncInProgress = false;
        this._peerLastPaths = null;
        this._hostLastPaths = null;
        this._hostPendingOps = null;
        this._transferStats = {
            filesUploaded: 0,
            filesDownloaded: 0,
            bytesUploaded: 0,
            bytesDownloaded: 0
        };

        // Show drive list
        this._hideMobileTopbar();
        document.getElementById('sync-drive-list').style.display = '';
        document.getElementById('sync-drive-detail').style.display = 'none';
        document.getElementById('sync-drive-lobby').style.display = 'none';

        this.renderDriveList();
        this.toastWarning(this._t('sync_drive_deleted_by_host'));
        this.addActivity('drive_removed', '\u540c\u6b65\u76d8\u5df2\u88ab\u5220\u9664');
    },

    // Connect to the global notification WebSocket channel.
    // This channel carries cross-drive events (drive_created, drive_deleted)
    // so that the drive list updates in real-time across all devices of the same user.
    _connectWSS() {
        if (!TL.api_token) {
            console.log('[SYNC] WSS skipped: no token');
            return;
        }
        if (this.signalingWS && (this.signalingWS.readyState === WebSocket.OPEN || this.signalingWS.readyState === WebSocket.CONNECTING)) {
            return; // Already connected or connecting
        }

        var self = this;
        var syncHost = this.SYNC_SERVER_HOST;
        var syncPort = this.SYNC_SERVER_PORT;

        // Clean up any stale WSS reference before creating a new one.
        // This prevents the old socket's onclose from firing and scheduling
        // a redundant reconnect.
        if (this.signalingWS) {
            var oldWS = this.signalingWS;
            oldWS.onopen = null;
            oldWS.onmessage = null;
            oldWS.onclose = null;
            oldWS.onerror = null;
            try { if (oldWS.readyState === WebSocket.OPEN || oldWS.readyState === WebSocket.CONNECTING) oldWS.close(); } catch (e) {}
            this.signalingWS = null;
        }

        try {
            var wsURL = 'wss://' + syncHost + ':' + syncPort + '/ws?token=' + encodeURIComponent(TL.api_token);
            console.log('[SYNC] Connecting WSS: ' + wsURL);
            this.signalingWS = new WebSocket(wsURL);

            this.signalingWS.onopen = function() {
                console.log('[SYNC] WSS connected');
                self._notifyReconnectDelay = 1000; // Reset reconnect delay
                // Register device on connection
                self.wsRequest('register_device', {
                    device_id: self.getDeviceId(),
                    device_name: self.deviceName || ''
                }, true);
                // Retry operations that failed while WSS was not connected.
                // loadDrives / _loadDeviceName are called during init() before
                // the WSS handshake completes; if the first connection attempt
                // fails they time out and need to be retried here.
                if (!self._drivesLoadSucceeded) {
                    console.log('[SYNC] Retrying loadDrives after WSS reconnect');
                    self.loadDrives();
                }
                if (!self._deviceNameLoaded) {
                    console.log('[SYNC] Retrying _loadDeviceName after WSS reconnect');
                    self._loadDeviceName();
                }
                // Re-register for drive presence if we're in a drive but the
                // server lost our drive state (WSS disconnect removes us).
                // Both Host and Peer need to re-enter to restore presence and
                // signaling routing.
                if (self.currentDrive) {
                    console.log('[SYNC] Re-entering drive after WSS reconnect');
                    self.wsRequest('drive_enter', {
                        drive_id: self.currentDrive.drive_id,
                        device_id: self.getDeviceId(),
                        device_name: self.deviceName || ''
                    }, true);
                }
            };

            this.signalingWS.onmessage = function(event) {
                // Binary frames are relay data
                if (event.data instanceof ArrayBuffer || event.data instanceof Blob) {
                    self._handleRelayBinaryFrame(event.data);
                    return;
                }
                try {
                    var msg = JSON.parse(event.data);
                    self._handleWSSMessage(msg);
                } catch (e) {
                    // Ignore parse errors
                }
            };

            this.signalingWS.onclose = function(e) {
                console.log('[SYNC] WSS closed: code=' + e.code);
                // Only auto-reconnect if we're not in the middle of cleanup
                if (self._notifyReconnectDelay === 30000) return; // destroy() called
                if (self._notifyReconnectDelay === undefined) {
                    self._notifyReconnectDelay = 1000;
                }
                if (self._notifyReconnectDelay < 30000) {
                    console.log('[SYNC] WSS reconnecting in ' + self._notifyReconnectDelay + 'ms');
                    setTimeout(function() {
                        self._connectWSS();
                    }, self._notifyReconnectDelay);
                    self._notifyReconnectDelay = Math.min(self._notifyReconnectDelay * 2, 30000);
                }
            };

            this.signalingWS.onerror = function(e) {
                console.warn('[SYNC] WSS error');
            };
        } catch (e) {
            console.warn('[SYNC] WSS connect failed: ' + e.message);
        }
    },

    // ========== WSS Relay Data Transfer ==========
    //
    // Binary Frame Protocol:
    //   [4B: drive_id_len] [drive_id] [4B: seq] [1B: payload_type_len] [payload_type] [payload]
    // All integers are big-endian.

    _encodeRelayFrame(driveId, payloadType, payload) {
        var driveIdBytes = new TextEncoder().encode(driveId);
        var payloadTypeBytes = new TextEncoder().encode(payloadType);
        var payloadBytes = payload instanceof ArrayBuffer ? new Uint8Array(payload) : new Uint8Array(payload);

        var totalLen = 4 + driveIdBytes.length + 4 + 1 + payloadTypeBytes.length + payloadBytes.length;
        var buf = new ArrayBuffer(totalLen);
        var view = new DataView(buf);
        var pos = 0;

        // drive_id_len (4 bytes, big-endian)
        view.setUint32(pos, driveIdBytes.length, false); pos += 4;
        // drive_id
        new Uint8Array(buf).set(driveIdBytes, pos); pos += driveIdBytes.length;
        // seq (4 bytes, big-endian)
        this._relaySeq++;
        view.setUint32(pos, this._relaySeq, false); pos += 4;
        // payload_type_len (1 byte)
        view.setUint8(pos, payloadTypeBytes.length); pos += 1;
        // payload_type
        new Uint8Array(buf).set(payloadTypeBytes, pos); pos += payloadTypeBytes.length;
        // payload
        new Uint8Array(buf).set(payloadBytes, pos);

        return buf;
    },

    _decodeRelayFrame(data) {
        var bytes = data instanceof ArrayBuffer ? new Uint8Array(data) : data;
        if (bytes.length < 9) return null;

        var view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
        var pos = 0;

        // drive_id_len
        var driveIdLen = view.getUint32(pos, false); pos += 4;
        if (pos + driveIdLen > bytes.length) return null;
        // drive_id
        var driveId = new TextDecoder().decode(bytes.slice(pos, pos + driveIdLen)); pos += driveIdLen;
        if (pos + 4 > bytes.length) return null;
        // seq
        var seq = view.getUint32(pos, false); pos += 4;
        if (pos + 1 > bytes.length) return null;
        // payload_type_len
        var payloadTypeLen = view.getUint8(pos); pos += 1;
        if (pos + payloadTypeLen > bytes.length) return null;
        // payload_type
        var payloadType = new TextDecoder().decode(bytes.slice(pos, pos + payloadTypeLen)); pos += payloadTypeLen;
        // payload
        var payload = bytes.slice(pos);

        return { driveId: driveId, seq: seq, payloadType: payloadType, payload: payload };
    },

    _sendRelayFrame(payloadType, payload) {
        if (!this.currentDrive) {
            console.warn('[SYNC] _sendRelayFrame: no current drive');
            return;
        }
        if (!this.signalingWS || this.signalingWS.readyState !== WebSocket.OPEN) {
            console.warn('[SYNC] _sendRelayFrame: WSS not open');
            return;
        }
        var frame = this._encodeRelayFrame(this.currentDrive.drive_id, payloadType, payload);
        this.signalingWS.send(frame);
    },

    async _handleRelayBinaryFrame(data) {
        var self = this;
        // Convert Blob to ArrayBuffer if needed
        var arrayBuf;
        if (data instanceof Blob) {
            arrayBuf = await data.arrayBuffer();
        } else {
            arrayBuf = data;
        }

        var frame = this._decodeRelayFrame(new Uint8Array(arrayBuf));
        if (!frame) {
            console.warn('[SYNC] Invalid relay frame received');
            return;
        }

        // Dedup: skip already-received seq numbers
        if (!this._relayReceivedSeq) this._relayReceivedSeq = new Set();
        if (this._relayReceivedSeq.has(frame.seq)) {
            console.log('[SYNC] Relay frame seq=' + frame.seq + ' already received, skipping');
            return;
        }
        this._relayReceivedSeq.add(frame.seq);
        // Keep the set from growing unbounded
        if (this._relayReceivedSeq.size > 10000) {
            this._relayReceivedSeq.clear();
        }

        console.log('[SYNC] Relay frame: seq=' + frame.seq + ' type=' + frame.payloadType + ' size=' + frame.payload.length);

        switch (frame.payloadType) {
            case 'file_chunk':
                this._handleRelayFileChunk(frame);
                break;
            case 'control':
                this._handleRelayControl(frame);
                break;
            default:
                console.log('[SYNC] Unknown relay payload type: ' + frame.payloadType);
        }
    },

    _handleRelayFileChunk(frame) {
        // Relay file chunks are processed the same way as DataChannel chunks.
        // The payload is a JSON-encoded chunk metadata that includes sha1, index, data, etc.
        try {
            var chunkMeta = JSON.parse(new TextDecoder().decode(frame.payload));
            // Forward to the existing chunk processing logic
            this._processFileChunk(chunkMeta, frame.payload);
        } catch (e) {
            console.warn('[SYNC] Failed to parse relay file chunk:', e);
        }
    },

    _handleRelayControl(frame) {
        try {
            var ctrlMsg = JSON.parse(new TextDecoder().decode(frame.payload));
            console.log('[SYNC] Relay control message:', ctrlMsg.type);
            this.handleP2PMessage(ctrlMsg);
        } catch (e) {
            console.warn('[SYNC] Failed to parse relay control message:', e);
        }
    },

    // ========== Connection Mode Management ==========

    _switchToRelayMode() {
        if (this._connectionMode === 'wss_relay') return;
        console.log('[SYNC] Switching to WSS relay mode');
        this._connectionMode = 'wss_relay';
        this._connState = 'connected';
        // Restart P2P probing to try to upgrade back to direct connection
        this._startP2PProbing();
    },

    _switchToP2PMode() {
        if (this._connectionMode === 'p2p') return;
        console.log('[SYNC] Switching to P2P direct mode');
        this._connectionMode = 'p2p';
        this._stopP2PProbing();
    },

    _startP2PProbing() {
        if (this._p2pProbeTimer) return;
        var self = this;
        console.log('[SYNC] Starting P2P probing (every 30s)');
        this._p2pProbeTimer = setInterval(function() {
            self._probeP2P();
        }, 30000);
    },

    _stopP2PProbing() {
        if (this._p2pProbeTimer) {
            clearInterval(this._p2pProbeTimer);
            this._p2pProbeTimer = null;
            console.log('[SYNC] P2P probing stopped');
        }
    },

    _probeP2P() {
        if (this._connectionMode !== 'wss_relay') return;
        console.log('[SYNC] Probing P2P connectivity...');
        var self = this;

        // Create a temporary RTCPeerConnection for probing
        var iceServers = this._getIceServers();
        var probePC = new RTCPeerConnection({
            iceServers: iceServers,
            iceTransportPolicy: 'all'
        });

        var probeTimeout = setTimeout(function() {
            console.log('[SYNC] P2P probe timeout — staying in relay mode');
            probePC.close();
        }, 15000);

        probePC.oniceconnectionstatechange = function() {
            if (probePC.iceConnectionState === 'connected' || probePC.iceConnectionState === 'completed') {
                clearTimeout(probeTimeout);
                console.log('[SYNC] P2P probe succeeded — upgrading to direct mode');
                probePC.close();
                self._switchToP2PMode();
                self.scheduleReconnect();
            }
        };

        // Create a probe DataChannel and send offer via signaling
        var dc = probePC.createDataChannel('p2p_probe');
        probePC.createOffer().then(function(offer) {
            return probePC.setLocalDescription(offer);
        }).then(function() {
            self.sendSignaling({
                type: 'webrtc_offer',
                sdp: probePC.localDescription,
                to_device: '*',
                probe: true
            });
        }).catch(function(e) {
            console.warn('[SYNC] P2P probe offer failed:', e);
            clearTimeout(probeTimeout);
            probePC.close();
        });

        probePC.onicecandidate = function(e) {
            if (e.candidate) {
                self.sendSignaling({
                    type: 'ice_candidate',
                    candidate: e.candidate,
                    to_device: '*',
                    probe: true
                });
            }
        };
    },

    // ========== Transport Abstraction Layer ==========
    //
    // Unified interface for sending data regardless of transport mode.

    _transportSend(data, metadata) {
        // Default to WSS relay; only use P2P DataChannel when explicitly in p2p mode
        if (this._connectionMode === 'p2p') {
            if (this.isHost) {
                return this._sendViaP2P(data, metadata);
            } else {
                return this._sendViaP2PToHost(data, metadata);
            }
        } else {
            return this._sendViaRelay(data, metadata);
        }
    },

    _sendViaP2P(data, metadata) {
        // Host: send to all peers or specific peer
        var self = this;
        if (metadata.target) {
            var conn = this._peerConnections[metadata.target];
            if (conn && conn.dc && conn.dc.readyState === 'open') {
                conn.dc.send(data);
                return Promise.resolve();
            }
        }
        // Broadcast to all peers
        var promises = [];
        Object.keys(this._peerConnections).forEach(function(peerId) {
            var conn = self._peerConnections[peerId];
            if (conn && conn.dc && conn.dc.readyState === 'open') {
                conn.dc.send(data);
                promises.push(Promise.resolve());
            }
        });
        return Promise.all(promises);
    },

    _sendViaP2PToHost(data, metadata) {
        // Peer: send to host via DataChannel
        if (this.rtcPeerConnection && this._dataChannel && this._dataChannel.readyState === 'open') {
            this._dataChannel.send(data);
            return Promise.resolve();
        }
        return Promise.reject(new Error('DataChannel not open'));
    },

    _sendViaRelay(data, metadata) {
        var payloadType = metadata.type || 'file_chunk';
        this._sendRelayFrame(payloadType, data);
        return Promise.resolve();
    },

    getTransportMode() {
        return this._connectionMode;
    },

    /**
     * Handle incoming WSS messages (unified message dispatch).
     * All message types flow through this single handler.
     */

    // 临时切换镜像到指定 session 执行 fn，完成后恢复。
    // 用于 WSS 消息路由到非活跃 session 时（不触发 UI 渲染）。
    _withSession(driveId, fn) {
        var prev = this.activeSessionId;
        if (prev !== driveId) {
            // 静默切换镜像（不渲染 UI）
            var session = this.sessions.get(driveId);
            if (!session) return;
            this.activeSessionId = driveId;
            this.currentDrive = session.drive;
            this.isHost = session.isHost;
            this._boundFolder = session.boundFolder;
            this._hostOnline = session.hostOnline;
            this._currentDrivePermission = session.permission;
            this.fileCache = session.fileCache;
            this._localFiles = session.localFiles;
            this._fileStatus = session.fileStatus;
            this._fileProgress = session.fileProgress;
            this.currentPath = session.currentPath;
            this.peers = session.peers;
            this.rtcPeerConnection = session.rtcPeerConnection;
            this._peerConnections = session.peerConnections;
            this._peerDeviceIds = session.peerDeviceIds;
            this.dataChannel = session.dataChannel;
            this.acceptDC = session.acceptDC;
            this._hostConnectionMode = session.hostConnectionMode;
            this._downloads = session.downloads;
            this._pendingDownloads = session.pendingDownloads;
            this._transferQueue = session.transferQueue;
            this._transferBusy = session.transferBusy;
            this._currentTransferSha1 = session.currentTransferSha1;
            this._transferStats = session.transferStats;
            this._peerLastPaths = session.peerLastPaths;
            this._hostLastPaths = session.hostLastPaths;
            this._hostPendingOps = session.hostPendingOps;
            this._syncTimer = session.syncTimer;
            this._syncInProgress = session.syncInProgress;
            this._scanInProgress = session.scanInProgress;
            this._lastScanFingerprints = session.lastScanFingerprints;
            this._connState = session.connState;
            this._reconnectTimer = session.reconnectTimer;
            this._reconnectAttempt = session.reconnectAttempt;
            this._iceTimeout = session.iceTimeout;
            this._connectTimeout = session.connectTimeout;
            this._offerInProgress = session.offerInProgress;
            this._offerTimeout = session.offerTimeout;
            this._pendingSignaling = session.pendingSignaling;
            this._connectionMode = session.connectionMode;
            this._relaySeq = session.relaySeq;
            this._relayReceivedSeq = session.relayReceivedSeq;
            this._syncStatus = session.syncStatus;
            this._fsObserver = session.fsObserver;
            this._activities = session.activities;
            this._detailTab = session.detailTab;
        }
        try {
            fn.call(this);
        } finally {
            if (prev !== driveId && prev) {
                // 恢复之前的活跃 session 镜像（不渲染 UI）
                var prevSession = this.sessions.get(prev);
                if (prevSession) {
                    this.activeSessionId = prev;
                    this.currentDrive = prevSession.drive;
                    this.isHost = prevSession.isHost;
                    this._boundFolder = prevSession.boundFolder;
                    this._hostOnline = prevSession.hostOnline;
                    this._currentDrivePermission = prevSession.permission;
                    this.fileCache = prevSession.fileCache;
                    this._localFiles = prevSession.localFiles;
                    this._fileStatus = prevSession.fileStatus;
                    this._fileProgress = prevSession.fileProgress;
                    this.currentPath = prevSession.currentPath;
                    this.peers = prevSession.peers;
                    this.rtcPeerConnection = prevSession.rtcPeerConnection;
                    this._peerConnections = prevSession.peerConnections;
                    this._peerDeviceIds = prevSession.peerDeviceIds;
                    this.dataChannel = prevSession.dataChannel;
                    this.acceptDC = prevSession.acceptDC;
                    this._hostConnectionMode = prevSession.hostConnectionMode;
                    this._downloads = prevSession.downloads;
                    this._pendingDownloads = prevSession.pendingDownloads;
                    this._transferQueue = prevSession.transferQueue;
                    this._transferBusy = prevSession.transferBusy;
                    this._currentTransferSha1 = prevSession.currentTransferSha1;
                    this._transferStats = prevSession.transferStats;
                    this._peerLastPaths = prevSession.peerLastPaths;
                    this._hostLastPaths = prevSession.hostLastPaths;
                    this._hostPendingOps = prevSession.hostPendingOps;
                    this._syncTimer = prevSession.syncTimer;
                    this._syncInProgress = prevSession.syncInProgress;
                    this._scanInProgress = prevSession.scanInProgress;
                    this._lastScanFingerprints = prevSession.lastScanFingerprints;
                    this._connState = prevSession.connState;
                    this._reconnectTimer = prevSession.reconnectTimer;
                    this._reconnectAttempt = prevSession.reconnectAttempt;
                    this._iceTimeout = prevSession.iceTimeout;
                    this._connectTimeout = prevSession.connectTimeout;
                    this._offerInProgress = prevSession.offerInProgress;
                    this._offerTimeout = prevSession.offerTimeout;
                    this._pendingSignaling = prevSession.pendingSignaling;
                    this._connectionMode = prevSession.connectionMode;
                    this._relaySeq = prevSession.relaySeq;
                    this._relayReceivedSeq = prevSession.relayReceivedSeq;
                    this._syncStatus = prevSession.syncStatus;
                    this._fsObserver = prevSession.fsObserver;
                    this._activities = prevSession.activities;
                    this._detailTab = prevSession.detailTab;
                }
            }
        }
    },

    _handleWSSMessage(msg) {
        console.log('[SYNC] WSS message: type=' + msg.type + ' drive_id=' + (msg.drive_id || 'none'));

        switch (msg.type) {
            // ========== Drive lifecycle events ==========
            case 'drive_created':
                if (msg.drive_id && this.currentDrive && this.currentDrive.drive_id === msg.drive_id) {
                    break; // This is the creating device itself
                }
                console.log('[SYNC] New drive created remotely: ' + (msg.drive_name || msg.drive_id));
                this.loadDrives();
                this.addActivity('drive_created_notify', '新同步盘已自动加入: ' + (msg.drive_name || msg.drive_id));
                break;

            case 'drive_deleted':
                if (this.sessions.has(msg.drive_id)) {
                    // 销毁对应 session（使用 _withSession 让 leaveDrive 操作正确 session）
                    this.leaveDrive(msg.drive_id);
                } else if (this.currentDrive && this.currentDrive.drive_id === msg.drive_id) {
                    this._handleDriveDeleted(msg.drive_id);
                } else {
                    console.log('[SYNC] Drive deleted remotely: ' + msg.drive_id);
                    this.drives = this.drives.filter(function(d) { return d.drive_id !== msg.drive_id; });
                    this.renderDriveList();
                }
                break;

            case 'new_notification':
                this.loadUnreadCount();
                // A new notification may carry the approval/rejection outcome for
                // one of our pending join requests — refresh the pending cards.
                this.loadMyJoinRequests();
                break;

            // ========== Join request status update (real-time applicant feedback) ==========
            case 'join_request_status':
                this._handleJoinRequestStatus(msg);
                break;

            // ========== Presence (peer online/offline) ==========
            case 'presence':
                // 更新对应 session 的 peers（若存在）；同时更新 drives 列表
                if (msg.drive_id && this.sessions.has(msg.drive_id)) {
                    var self1 = this;
                    this._withSession(msg.drive_id, function() {
                        self1._handlePresenceNotification(msg);
                    });
                } else {
                    this._handlePresenceNotification(msg);
                }
                break;

            // ========== Drive status update (host online/offline) ==========
            case 'drive_status_update':
                this._handleDriveStatusUpdate(msg);
                // 同步更新 session.hostOnline
                var payload = msg.payload || msg;
                var hostOnline = payload.host_online;
                if (msg.drive_id && this.sessions.has(msg.drive_id)) {
                    var session = this.sessions.get(msg.drive_id);
                    session.hostOnline = !!hostOnline;
                    if (this.activeSessionId === msg.drive_id) {
                        this._hostOnline = !!hostOnline;
                    }
                }
                break;

            // ========== Peer list ==========
            case 'peer_list':
                if (msg.drive_id && this.sessions.has(msg.drive_id)) {
                    var self2 = this;
                    this._withSession(msg.drive_id, function() {
                        self2._handlePeerList(msg);
                    });
                } else {
                    this._handlePeerList(msg);
                }
                break;

            // ========== Sync control messages (P2P relay) ==========
            case 'sync_control':
                if (msg.drive_id && this.sessions.has(msg.drive_id)) {
                    var self3 = this;
                    this._withSession(msg.drive_id, function() {
                        var payload = msg.payload;
                        if (typeof payload === 'string') {
                            try { payload = JSON.parse(payload); } catch(e) { return; }
                        }
                        var msgType = payload._msg_type || payload.msg_type || msg.type;
                        var wsm = {
                            msg_type: msgType,
                            from_device: msg.from_device,
                            payload: payload
                        };
                        self3.handleP2PMessage(wsm);
                    });
                }
                break;

            // ========== WebRTC signaling ==========
            case 'webrtc_offer':
            case 'webrtc_answer':
            case 'ice_candidate':
                if (msg.drive_id && this.sessions.has(msg.drive_id)) {
                    var self4 = this;
                    this._withSession(msg.drive_id, function() {
                        self4.handleSignalingMessage(msg);
                    });
                }
                break;

            // ========== WebRTC renegotiation (Host-side) ==========
            case 'webrtc_renegotiate':
                if (msg.drive_id && this.sessions.has(msg.drive_id)) {
                    var self5 = this;
                    this._withSession(msg.drive_id, function() {
                        self5._handleWebRTCRenegotiate(msg);
                    });
                }
                break;

            // ========== Response types (for request/response matching) ==========
            case 'drive_enter_resp':
                // Apply authoritative permission from server before resolving
                // any pending wsRequest. drive_enter_resp.permission is the
                // server's source of truth (catches mid-session revocation /
                // expiration that drive_list doesn't reflect yet).
                if (msg.payload && msg.payload.permission) {
                    this._currentDrivePermission = msg.payload.permission;
                    if (!this.isHost) {
                        console.log('[SYNC] drive_enter_resp permission=' + msg.payload.permission);
                    }
                }
                if (msg.request_id) {
                    this.handleWsResponse(msg.request_id, msg.payload || msg.data || {});
                }
                break;

            case 'register_device_resp':
            case 'drive_list_resp':
            case 'drive_create_resp':
            case 'drive_join_resp':
            case 'drive_delete_resp':
            case 'drive_leave_resp':
            case 'device_get_resp':
            case 'device_set_resp':
            case 'sync_control_ack':
            case 'offline_poll_resp':
            case 'heartbeat_ack':
            case 'invite_code_create_resp':
            case 'invite_code_list_resp':
            case 'invite_code_revoke_resp':
            case 'join_request_apply_resp':
            case 'join_request_list_resp':
            case 'my_join_requests_resp':
            case 'join_request_approve_resp':
            case 'join_request_reject_resp':
            case 'join_request_revoke_resp':
            case 'notification_list_resp':
            case 'notification_mark_read_resp':
            case 'notification_mark_all_read_resp':
            case 'unread_count_resp':
            case 'error':
                if (msg.request_id) {
                    this.handleWsResponse(msg.request_id, msg.payload || msg.data || {});
                }
                break;
        }
    },

    /**
     * Handle presence notification (peer/host online/offline).
     */
    _handlePresenceNotification(msg) {
        var payload = msg.payload || {};
        if (typeof payload === 'string') {
            try { payload = JSON.parse(payload); } catch(e) { return; }
        }
        console.log('[SYNC] Presence: drive=' + msg.drive_id + ' uid=' + payload.uid + ' role=' + payload.role + ' online=' + payload.online + ' device=' + payload.device_name);

        // Adapt to legacy peer_status format for _handlePeerStatusNotification
        this._handlePeerStatusNotification({
            drive_id: msg.drive_id,
            uid: payload.uid,
            role: payload.role,
            online: payload.online,
            device_id: payload.device_id,
            device_name: payload.device_name
        });
    },

    /**
     * Handle drive status update (host online/offline).
     * Pushed by server to ALL connected devices of the user, including those
     * in the lobby that haven't entered the drive yet. This ensures real-time
     * status updates without polling.
     */
    _handleDriveStatusUpdate(msg) {
        var payload = msg.payload;
        if (typeof payload === 'string') {
            try { payload = JSON.parse(payload); } catch(e) { return; }
        }
        // BroadcastToUser sends fields at top level (no payload wrapper).
        // Fall back to msg itself when payload is absent.
        if (!payload) {
            payload = msg;
        }
        var driveId = msg.drive_id;
        var hostOnline = payload.host_online;
        var deviceId = payload.device_id;
        var deviceName = payload.device_name;

        console.log('[SYNC] Drive status update: drive=' + driveId + ' host_online=' + hostOnline + ' device=' + deviceName);

        // Don't process our own status changes (we already know our own state)
        if (deviceId === this.getDeviceId()) {
            return;
        }

        // Update the drive in the drives list
        for (var i = 0; i < this.drives.length; i++) {
            if (this.drives[i].drive_id === driveId) {
                this.drives[i].host_online = hostOnline ? 1 : 0;
                break;
            }
        }

        // Re-render the drive list (lobby card view) to reflect the updated status
        if (typeof this.renderDriveList === 'function') {
            this.renderDriveList();
        }

        // If we're a Peer, update lobby/detail views
        if (!this.isHost) {
            var wasOnline = this._hostOnline;
            this._hostOnline = !!hostOnline;

            // Check if we're in the lobby view for this drive
            var lobbyEl = document.getElementById('sync-drive-lobby');
            var inLobby = lobbyEl && lobbyEl.style.display !== 'none' &&
                          this.currentDrive && this.currentDrive.drive_id === driveId;

            if (inLobby) {
                // Update lobby UI
                this.showLobby();

                if (hostOnline && !wasOnline) {
                    console.log('[SYNC] Host came online while in lobby, auto-entering drive');
                    var self = this;
                    setTimeout(function() {
                        self.enterDrive(driveId);
                    }, 100);
                }
            } else if (this.currentDrive && this.currentDrive.drive_id === driveId) {
                // We're in the drive detail view
                if (!hostOnline && wasOnline) {
                    console.log('[SYNC] Host went offline (drive_status_update)');
                    this._connState = 'disconnected';
                    this._showHostOffline();
                    this.stopPeriodicSync();
                    // Close the old WebRTC connection (same reason as _handlePeerStatusNotification)
                    if (this.rtcPeerConnection) {
                        try { this.rtcPeerConnection.close(); } catch (e) {}
                        this.rtcPeerConnection = null;
                    }
                    if (this.acceptDC) {
                        try { this.acceptDC.close(); } catch (e) {}
                        this.acceptDC = null;
                    }
                }
            }
        }
    },

    /**
     * Handle peer list update from server.
     * Populates _peerDeviceIds for P2P message routing, and if Host,
     * triggers offer creation for already-online peers.
     */
    _handlePeerList(msg) {
        var payload = msg.payload || [];
        if (typeof payload === 'string') {
            try { payload = JSON.parse(payload); } catch(e) { payload = []; }
        }
        console.log('[SYNC] Peer list: ' + payload.length + ' peers');
        this.peers = payload;

        // Populate _peerDeviceIds for P2P message routing
        if (!this._peerDeviceIds) this._peerDeviceIds = {};
        for (var i = 0; i < payload.length; i++) {
            var p = payload[i];
            if (p.device_id && p.peer_id) {
                this._peerDeviceIds[p.device_id] = p.peer_id;
            }
        }

        this.updatePeerList();

        // Host: create offers for all online peers that don't have a connection yet.
        // Per-peer architecture: each Peer gets its own RTCPeerConnection.
        if (this.isHost && payload.length > 0) {
            var self = this;
            payload.forEach(function(p) {
                if (p.device_id && !self._peerConnections[p.device_id]) {
                    console.log('[SYNC] Host creating offer for online peer: ' + p.device_id);
                    self._createOfferForPeer(p.device_id, p.device_name || '');
                }
            });
        }

        // Peer: check if Host is in the peer list.
        // When the Peer enters the drive with stale host_online=0, the Host might
        // already be in the drive. The presence(host, online) broadcast was sent
        // BEFORE the Peer entered, so the Peer missed it. The peer_list is the
        // only way to discover the Host is already online.
        if (!this.isHost && this.currentDrive) {
            var hostEntry = null;
            for (var j = 0; j < payload.length; j++) {
                var entry = payload[j];
                if (entry.peer_id && entry.peer_id.indexOf('host_') === 0) {
                    hostEntry = entry;
                    break;
                }
            }

            if (hostEntry && !this._hostOnline) {
                console.log('[SYNC] Host found in peer_list (was offline), transitioning to online');
                this._hostOnline = true;
                // Update drive in drives list so enterDrive() reads correct status
                for (var k = 0; k < this.drives.length; k++) {
                    if (this.drives[k].drive_id === this.currentDrive.drive_id) {
                        this.drives[k].host_online = 1;
                        break;
                    }
                }
                // Re-enter drive to initialize WebRTC and connect to Host.
                // enterDrive() will see _hostOnline=true (from updated drive list)
                // and proceed through the normal connection flow.
                var reEntrySelf = this;
                setTimeout(function() {
                    reEntrySelf.enterDrive(reEntrySelf.currentDrive.drive_id);
                }, 0);
            } else if (!hostEntry && this._hostOnline && !this.isHost) {
                // Host was online but is no longer in the peer list
                console.log('[SYNC] Host not in peer_list (was online), transitioning to offline');
                this._hostOnline = false;
                this._connState = 'disconnected';
                this._showHostOffline();
                this.stopPeriodicSync();
                if (this.rtcPeerConnection) {
                    try { this.rtcPeerConnection.close(); } catch (e) {}
                    this.rtcPeerConnection = null;
                }
                if (this.acceptDC) {
                    try { this.acceptDC.close(); } catch (e) {}
                    this.acceptDC = null;
                }
            }
        }
    },

    // 清理指定 session 的连接与定时器（不影响其它 session）。
    // 若 session 是当前活跃 session，同步清理 this.xxx 镜像字段。
    _cleanupSessionConnection(session) {
        if (!session) return;
        console.log('[SYNC] Cleaning up session ' + session.drive_id + ': reconnectTimer=' + !!session.reconnectTimer + ' RTCPC=' + !!session.rtcPeerConnection + ' peerCons=' + Object.keys(session.peerConnections || {}).length);

        // 停止同步、心跳、FS 观察
        this._stopSessionSync(session);

        // 清理定时器
        if (session.reconnectTimer) { clearTimeout(session.reconnectTimer); session.reconnectTimer = null; }
        if (session.iceTimeout) { clearTimeout(session.iceTimeout); session.iceTimeout = null; }
        if (session.connectTimeout) { clearTimeout(session.connectTimeout); session.connectTimeout = null; }
        if (session.offerTimeout) { clearTimeout(session.offerTimeout); session.offerTimeout = null; }
        session.reconnectAttempt = 0;
        session.offerInProgress = false;
        session.pendingSignaling = null;
        session.connState = 'disconnected';
        session.connectionMode = 'wss_relay';

        // drive_leave（WSS 是 per-user 共享，不为单个 session 关闭）
        if (this.signalingWS && this.signalingWS.readyState === WebSocket.OPEN) {
            this.wsRequest('drive_leave', { drive_id: session.drive_id }, true);
        }

        // 关闭 RTC
        if (session.rtcPeerConnection) {
            try { session.rtcPeerConnection.close(); } catch (e) {}
            session.rtcPeerConnection = null;
        }
        Object.keys(session.peerConnections).forEach(function(pid) {
            var conn = session.peerConnections[pid];
            try { if (conn.pc) conn.pc.close(); } catch (e) {}
            if (conn.dc) { try { conn.dc.close(); } catch (e) {} }
        });
        session.peerConnections = {};
        session.dataChannel = null;
        session.acceptDC = null;
        session.peerDeviceIds = {};
        session.pendingDownloads = null;
        if (session.pendingDownloadTimeout) {
            clearTimeout(session.pendingDownloadTimeout);
            session.pendingDownloadTimeout = null;
        }

        // 若清理的是 active session，同步镜像字段并调用依赖 this.xxx 的辅助方法
        if (this.activeSessionId === session.drive_id) {
            // 这些方法操作 this.xxx 镜像字段，仅对 active session 有效
            try { this._stopHeartbeat(); } catch (e) {}
            try { this._clearJoinRetry(); } catch (e) {}
            try { this._stopP2PProbing(); } catch (e) {}

            this.rtcPeerConnection = null;
            this._peerConnections = {};
            this._peerDeviceIds = {};
            this.dataChannel = null;
            this.acceptDC = null;
            this._pendingDownloads = null;
            this._connState = 'disconnected';
            this._reconnectTimer = null;
            this._iceTimeout = null;
            this._connectTimeout = null;
            this._offerInProgress = false;
            this._offerTimeout = null;
            this._pendingSignaling = null;
            this._connectionMode = 'wss_relay';
            this._syncTimer = null;
            this._immediateSyncTimer = null;
            this._fsObserver = null;
            this._eligiblePeers = [];
            this._hostConnectionMode = 'unknown';
            if (this._pendingDownloadTimeout) {
                clearTimeout(this._pendingDownloadTimeout);
                this._pendingDownloadTimeout = null;
            }
        }
    },

    // 停止指定 session 的同步与 FS 观察
    _stopSessionSync(session) {
        if (!session) return;
        if (session.syncTimer) { clearTimeout(session.syncTimer); session.syncTimer = null; }
        // 兼容旧字段名 _syncTimer / _immediateSyncTimer
        if (session._syncTimer) { clearTimeout(session._syncTimer); session._syncTimer = null; }
        if (session._immediateSyncTimer) { clearTimeout(session._immediateSyncTimer); session._immediateSyncTimer = null; }
        if (session.fsObserver) {
            try { session.fsObserver.disconnect(); } catch (e) {}
            session.fsObserver = null;
        }
        // 若是 active session，也清理 this.xxx 镜像
        if (this.activeSessionId === session.drive_id) {
            try { this.stopPeriodicSync(); } catch (e) {}
        }
    },

    _cleanupConnection() {
        // 兼容包装：清理当前活跃 session
        this._cleanupSessionConnection(this._getActiveSession());
    },

    leaveDrive(driveId) {
        driveId = driveId || (this.currentDrive ? this.currentDrive.drive_id : null);
        if (!driveId) {
            console.warn('[SYNC] leaveDrive: no drive to leave');
            return;
        }
        this.trackUI('sync_leave_drive');
        console.log('[SYNC] Leaving drive: ' + driveId);

        var session = this.sessions.get(driveId);
        var wasActive = (this.activeSessionId === driveId);

        // 切换镜像到该 session 以保存状态（_saveSyncState 操作 this.xxx 镜像）
        if (session && !wasActive) {
            this.switchSession(driveId);
        }

        // Persist sync state so next session resumes correctly
        if (session) {
            this._saveSyncState();
            this._cleanupSessionConnection(session);
        }

        if (driveId) {
            this._removeStoredFolderHandle(driveId);
        }

        // 释放文件夹锁文件（异步，不阻塞）
        if (session) {
            var self = this;
            this._releaseFolderLock(session).then(function() {});
        }
        this._bcast('drive_unlocked', { drive_id: driveId });

        // 从 sessions Map 移除
        this.sessions.delete(driveId);

        // 切换到下一个 session 或返回列表
        if (wasActive || this.activeSessionId === driveId) {
            this.activeSessionId = null;
            if (this.sessions.size > 0) {
                this.switchSession(this.sessions.keys().next().value);
            } else {
                // 清空镜像字段
                this.currentDrive = null;
                this.isHost = false;
                this._hostOnline = true;
                this.fileCache.clear();
                this._localFiles = [];
                this._fileStatus.clear();
                this._fileProgress.clear();
                this._currentTransferSha1 = null;
                this._downloads.clear();
                this.peers = [];
                this._boundFolder = null;
                this._connectionMode = 'wss_relay';
                this._transferStats = {
                    filesUploaded: 0,
                    filesDownloaded: 0,
                    bytesUploaded: 0,
                    bytesDownloaded: 0
                };

                this._hideMobileTopbar();
                this._renderSessionSwitcher();
                var list = document.getElementById('sync-drive-list');
                var detail = document.getElementById('sync-drive-detail');
                var lobby = document.getElementById('sync-drive-lobby');
                if (list) list.style.display = '';
                if (detail) detail.style.display = 'none';
                if (lobby) lobby.style.display = 'none';
            }
        } else {
            // 非活跃 session 被销毁，仅刷新切换器
            this._renderSessionSwitcher();
        }
    },

    // ========== Delete / Leave Drive ==========
    _pendingDeleteDrive: null,

    promptDeleteDrive(driveId, event) {
        if (event) event.stopPropagation();
        var drive = this.drives.find(function(r) { return r.drive_id === driveId; });
        if (!drive) {
            console.warn('[SYNC] promptDeleteDrive: drive not found id=' + driveId);
            return;
        }
        this._pendingDeleteDrive = driveId;

        var myDeviceId = this.getDeviceId();
        var isHost = (drive.host_device_id && drive.host_device_id === myDeviceId);
        var driveName = drive.name || drive.drive_name || '未命名同步盘';
        var titleEl = document.getElementById('sync-delete-title');
        var msgEl = document.getElementById('sync-delete-message');
        var confirmBtn = document.getElementById('sync-delete-confirm-btn');
        var confirmText = confirmBtn ? confirmBtn.querySelector('span') : null;

        if (isHost) {
            if (titleEl) titleEl.textContent = '删除同步盘';
            if (msgEl) msgEl.innerHTML = '确定要删除同步盘 <strong>' + this.escapeHtml(driveName) + '</strong> 吗？<br><br>' +
                '<span style="color:var(--vx-text-secondary);font-size:13px">' +
                this._t('sync_delete_host_warning') + '<br>' +
                '<strong>' + this._t('sync_delete_local_safe') + '</strong></span>';
            if (confirmText) confirmText.textContent = '确认删除';
        } else {
            if (titleEl) titleEl.textContent = '退出同步盘';
            if (msgEl) msgEl.innerHTML = '确定要退出同步盘 <strong>' + this.escapeHtml(driveName) + '</strong> 吗？<br><br>' +
                '<span style="color:var(--vx-text-secondary);font-size:13px">' +
                '退出后将不再接收该同步盘的文件更新。<br>' +
                '<strong>本地已同步的文件不会被删除。</strong></span>';
            if (confirmText) confirmText.textContent = '确认退出';
        }

        VXUI.openModal('sync-delete-modal');
    },

    cancelDeleteDrive() {
        this._pendingDeleteDrive = null;
        VXUI.closeModal('sync-delete-modal');
    },

    async confirmDeleteDrive() {
        if (!this._pendingDeleteDrive) return;
        var driveId = this._pendingDeleteDrive;
        var drive = this.drives.find(function(r) { return r.drive_id === driveId; });
        var isHost = drive && drive.host_device_id && drive.host_device_id === this.getDeviceId();
        this.trackUI(isHost ? 'sync_delete_drive' : 'sync_leave_drive_list');
        this._pendingDeleteDrive = null;
        VXUI.closeModal('sync-delete-modal');

        // If currently in this drive, leave first
        if (this.currentDrive && this.currentDrive.drive_id === driveId) {
            this.leaveDrive();
        }

        this.showLoading('正在删除...');
        var rsp = await this._post('drive_delete', {
            drive_id: driveId,
            device_id: this.getDeviceId()
        });
        this.hideLoading();

        if (rsp.status === 1) {
            var role = rsp.data.role || 'peer';
            var driveName = '';
            var drive = this.drives.find(function(r) { return r.drive_id === driveId; });
            if (drive) driveName = drive.name || drive.drive_name || '同步盘';

            // Remove from local list
            this.drives = this.drives.filter(function(r) { return r.drive_id !== driveId; });
            this.renderDriveList();

            // Clean up stored folder handle
            this._removeStoredFolderHandle(driveId);

            if (role === 'host') {
                this.toastSuccess(this._t('sync_drive_deleted').replace('{name}', driveName));
                this.addActivity('drive_delete', '删除同步盘 ' + driveName);
            } else {
                this.toastSuccess(this._t('sync_drive_left').replace('{name}', driveName));
                this.addActivity('drive_leave', '退出同步盘 ' + driveName);
            }
            console.log('[SYNC] Drive deleted/left: id=' + driveId + ' role=' + role);
        } else {
            console.warn('[SYNC] drive_delete failed: ' + (rsp.debug || 'unknown'));
            this.toastError(rsp.debug || this._t('sync_delete_failed'));
        }
    },

    uploadFiles() {
        if (!this._isHostAlive()) return;
        if (!this._currentUserHasWritePermission()) {
            VXUI.showMsg(this._t('read_only_permission_denied'), 'error');
            return;
        }
        this.trackUI('sync_upload_files');
        const input = document.getElementById('sync-file-input');
        if (input) input.click();
    },
    
    handleFileSelect(event) {
        if (!this._isHostAlive()) return;
        if (!this._currentUserHasWritePermission()) {
            VXUI.showMsg(this._t('read_only_permission_denied'), 'error');
            return;
        }
        this.trackUI('sync_file_select');
        const files = event.target.files;
        if (!files || files.length === 0) return;
        
        Array.from(files).forEach(file => this.uploadFile(file));
        
        // Reset input
        event.target.value = '';
    },
    
    async downloadFile(sha1) {
        this.trackUI('sync_download_file');
        if (this.isHost) {
            // Host: read directly from bound folder
            var file = await this.getFileFromFileSystem(sha1);
            if (file) {
                var url = URL.createObjectURL(file.blob);
                var a = document.createElement('a');
                a.href = url;
                a.download = file.name || sha1;
                document.body.appendChild(a);
                a.click();
                document.body.removeChild(a);
                URL.revokeObjectURL(url);
                console.log('[SYNC] Downloaded from filesystem: ' + file.name + ' size=' + file.size);
            } else {
                console.warn('[SYNC] Host download failed: file not found in bound folder');
                this.toastError(this._t('sync_file_not_found'));
            }
        } else {
            // Peer: request file from Host via P2P DataChannel
            console.log('[SYNC] Requesting remote download: sha1=' + sha1);
            var dc = this.acceptDC;
            if (!dc || dc.readyState !== 'open') {
                this.toastError(this._t('sync_not_connected_to_host'));
                return;
            }
            this.sendToDC({ t: 'file_download_req', d: { sha1 } });
        }
    },
    
    showProgress(fileName, transferred, total) {
        var sha1 = this._currentTransferSha1;
        if (sha1) {
            this._updateFileRow(sha1);
        }
        this.updateStatus('syncing');
    },

    updateProgress(transferred, total) {
        // No longer update progress UI
    },

    hideProgress() {
        var sha1 = this._currentTransferSha1;
        if (sha1) {
            this._fileStatus.set(sha1, 'synced');
            this._updateFileRow(sha1);
        }
        this._currentTransferSha1 = null;
        this.updateStatus('ready');
    },
    
    // Enqueue a file download request (serialize one at a time to avoid chunk interleaving)
    _enqueueTransfer(sha1, dc) {
        this._transferQueue.push({ type: 'download', sha1: sha1, dc: dc });
        if (!this._transferBusy) {
            this._processNextTransfer();
        }
    },

    _enqueueUpload(f) {
        this._transferQueue.push({ type: 'upload', file: f });
        if (!this._transferBusy) {
            this._processNextTransfer();
        }
    },
    
    async _processNextTransfer() {
        if (this._transferQueue.length === 0) {
            this._transferBusy = false;
            return;
        }
        this._transferBusy = true;
        var task = this._transferQueue.shift();
        try {
            if (task.type === 'upload') {
                await this.uploadFileToHost(task.file.sha1, task.file.meta);
            } else {
                await this.sendFileChunk(task.sha1 || task, task.dc);
            }
        } catch (e) {
            console.error('[SYNC] Transfer failed for ' + (task.sha1 || (task.file && task.file.name)) + ': ', e);
            console.log('[SYNC] Retrying connection after transfer failure');
            this.scheduleReconnect();
        }
        // Process next after this one completes
        this._processNextTransfer();
    },
    
    async sendFileChunk(sha1, dc) {
        // Host: read file from bound folder, then send chunks to the requesting Peer's DC
        var file = await this.getFileFromFileSystem(sha1);
        if (!file) {
            console.warn('[SYNC] File not found in bound folder for sendFileChunk: ' + sha1);
            return;
        }

        // Track per-file status for the Host
        this._currentTransferSha1 = sha1;
        this._fileStatus.set(sha1, 'uploading');
        this._updateFileRow(sha1);
        // Init upload transfer tracking
        this._transferStartTime = Date.now();
        this._transferLastBytes = 0;
        this._transferLastTime = Date.now();
        this._transferSpeed = 0;
        // Determine target node and mode for upload
        var uploadTargetNode = '';
        var uploadMode = 'unknown';
        if (this.isHost && dc) {
            // Find which peer this DC belongs to
            var peerDeviceId = null;
            Object.keys(this._peerConnections).forEach(function(pid) {
                if (VX_SYNC._peerConnections[pid].dc === dc) { peerDeviceId = pid; }
            });
            if (peerDeviceId && this._peerConnections[peerDeviceId]) {
                uploadTargetNode = this._peerConnections[peerDeviceId].displayName || peerDeviceId;
                uploadMode = this._peerConnections[peerDeviceId].mode || 'unknown';
            }
        } else {
            uploadTargetNode = '\u4e3b\u673a';
            uploadMode = this._hostConnectionMode || 'unknown';
        }
        this.upsertTransferActivity('upload', file.name || sha1, sha1, 0, '', uploadMode, uploadTargetNode);

        // Send metadata first so Peer knows what's coming
        // Include parent_path and sync flag for bidirectional sync
        var meta = this.fileCache.get(sha1);
        var startMeta = { sha1: sha1, name: file.name, size: file.size, sync: true };
        if (meta && meta.parent_path) {
            startMeta.parent_path = meta.parent_path;
        }
        this.sendToDC({ t: 'file_upload_start', d: startMeta }, dc);

        var CHUNK_SIZE = this.CHUNK_SIZE;
        var totalChunks = Math.ceil(file.size / CHUNK_SIZE);
        var BUFFER_THRESHOLD = 4 * 1024 * 1024; // 4MB backpressure threshold
        var blob = file.blob;
        var self = this;

        console.log('[SYNC] Sending file chunks: name=' + (file.name || sha1) + ' size=' + file.size + ' chunks=' + totalChunks);

        for (var i = 0; i < totalChunks; i++) {
            var start = i * CHUNK_SIZE;
            var end = Math.min(start + CHUNK_SIZE, file.size);
            var chunk = blob.slice(start, end);
            var buffer = await chunk.arrayBuffer();

            var targetDC = this.isHost ? dc : this.acceptDC;
            if (!targetDC || targetDC.readyState !== 'open') {
                console.warn('[SYNC] DC closed during chunk send at ' + (i + 1) + '/' + totalChunks + ' for ' + sha1);
                this._fileStatus.set(sha1, 'synced');
                this._updateFileRow(sha1);
                this._removeTransferActivity(sha1);
                this.addActivity('upload', '\u53d1\u9001\u4e2d\u65ad: ' + (file.name || sha1), { source: this._t('sync_this_device'), target: uploadTargetNode, mode: uploadMode });
                return;
            }

            // Event-based backpressure: wait for buffer to drain if needed
            var ok = await this._waitForBufferDrain(targetDC, BUFFER_THRESHOLD);
            if (!ok) {
                console.warn('[SYNC] DC closed during backpressure wait at chunk ' + (i + 1) + '/' + totalChunks);
                this._fileStatus.set(sha1, 'synced');
                this._updateFileRow(sha1);
                this._removeTransferActivity(sha1);
                this.addActivity('upload', '\u53d1\u9001\u4e2d\u65ad: ' + (file.name || sha1), { source: this._t('sync_this_device'), target: uploadTargetNode, mode: uploadMode });
                return;
            }

            targetDC.send(buffer);
            // Update upload progress every 5 chunks
            var bytesSent = end;
            if ((i + 1) % 5 === 0 || i === totalChunks - 1) {
                var now = Date.now();
                var elapsed = (now - self._transferLastTime) / 1000;
                if (elapsed > 0.5) {
                    var bytesDelta = bytesSent - self._transferLastBytes;
                    self._transferSpeed = bytesDelta / elapsed;
                    self._transferLastBytes = bytesSent;
                    self._transferLastTime = now;
                    var progress = (bytesSent / file.size * 100);
                    self.upsertTransferActivity('upload', file.name || sha1, sha1, progress, self._formatSpeed(self._transferSpeed), uploadMode, uploadTargetNode);
                }
            }
            this._updateFileRow(sha1);
            if ((i + 1) % 10 === 0 || i === totalChunks - 1) {
                console.log('[SYNC] Sent chunk ' + (i + 1) + '/' + totalChunks + ' for ' + sha1);
            }
        }

        // Wait for buffer to flush before signaling completion
        var dcDone = this.isHost ? dc : this.acceptDC;
        if (dcDone && dcDone.readyState === 'open') {
            await this._waitForBufferDrain(dcDone, 0);
        }

        this.sendToDC({ t: 'file_upload_done', d: { sha1: sha1 } }, dc);
        console.log('[SYNC] All chunks sent for ' + sha1);

        // Mark file as synced
        this._fileStatus.set(sha1, 'synced');
        this._updateFileRow(sha1);
        this._removeTransferActivity(sha1);
        this.addActivity('upload', '\u53d1\u9001\u5b8c\u6210: ' + (file.name || sha1), { source: this._t('sync_this_device'), target: uploadTargetNode, mode: uploadMode });
    },

    resolveConflict(choice) {
        if (!this.pendingConflict) return;
        
        console.log('[SYNC] Resolving conflict for ' + this.pendingConflict.sha1 + ': choice=' + choice);
        if (choice === 'remote') {
            this.sendToDC({ t: 'file_download_req', d: { sha1: this.pendingConflict.sha1 } });
        } else {
            console.log('[SYNC] Keeping local version of ' + this.pendingConflict.sha1);
        }
        
        this.pendingConflict = null;
        VXUI.closeModal('sync-conflict-modal');
    },
    
    async handleRemoteDelete(sha1, source) {
        var file = this.fileCache.get(sha1);
        var fileName = file ? file.name : sha1;
        // Delete from local FS so it doesn't reappear on the next scan
        if (file && this._boundFolder && this._boundFolder.handle) {
            await this._deleteLocalFile(file.parent_path || '/', file.name);
        }
        console.log('[SYNC] Remote delete:', sha1);
        this.fileCache.delete(sha1);
        this._fileStatus.delete(sha1);
        this._fileProgress.delete(sha1);
        // Also remove from local files list
        this._localFiles = (this._localFiles || []).filter(function(f) { return f.sha1 !== sha1; });
        this.renderFileList(Array.from(this.fileCache.values()));
        this.addActivity('delete', fileName, { source: source || this._t('sync_this_device'), target: this._t('sync_this_device') });
    },
    
    handleRemoteRename(sha1, newName, newSha1, source) {
        console.log('[SYNC] Remote rename:', sha1, '->', newName);
        var entry = this.fileCache.get(sha1);
        if (!entry) return;
        var oldName = entry.name;
        var oldPath = (entry.parent_path || '/') + '/' + oldName;

        // Rename local FS file
        this._renameLocalFile(oldPath, newName).then(function(ok) {
            if (!ok) console.warn('[SYNC] Remote rename: local FS rename failed for ' + oldName);
        });

        // Update cache: remove old sha1, set new entry with new sha1
        this.fileCache.delete(sha1);
        var newEntry = {
            sha1: newSha1 || sha1,
            name: newName,
            size: entry.size,
            parent_path: entry.parent_path || '/',
            mtime: Date.now()
        };
        this.fileCache.set(newEntry.sha1, newEntry);
        this.renderFileList(Array.from(this.fileCache.values()));
        this.addActivity('rename', oldName + ' \u2192 ' + newName, { source: source || this._t('sync_this_device'), target: this._t('sync_this_device') });
    },

    handleRemoteMove(sha1, newParentPath, newSha1, source) {
        console.log('[SYNC] Remote move:', sha1, '->', newParentPath);
        var entry = this.fileCache.get(sha1);
        if (!entry) return;
        var oldPath = (entry.parent_path || '/') + '/' + entry.name;

        // Move local FS file
        this._moveLocalFile(oldPath, newParentPath).then(function(ok) {
            if (!ok) console.warn('[SYNC] Remote move: local FS move failed for ' + entry.name);
        });

        // Update cache: remove old sha1, set new entry with new sha1
        this.fileCache.delete(sha1);
        var newEntry = {
            sha1: newSha1 || sha1,
            name: entry.name,
            size: entry.size,
            parent_path: newParentPath,
            mtime: Date.now()
        };
        this.fileCache.set(newEntry.sha1, newEntry);
        this.renderFileList(Array.from(this.fileCache.values()));
        this.addActivity('move', entry.name + ' \u2192 ' + newParentPath, { source: source || this._t('sync_this_device'), target: this._t('sync_this_device') });
    },
    
    async handleRemoteMkdir(data, source) {
        console.log('[SYNC] Remote mkdir:', data.name);
        var folderPath = data.parent_path || '/';
        // Create folder in local FS so it appears on the next scan
        if (this._boundFolder && this._boundFolder.handle) {
            await this._createLocalFolder(folderPath, data.name);
        }
        this.addActivity('create_folder', data.name, { source: source || this._t('sync_this_device'), target: this._t('sync_this_device') });
        // Only add to cache if the folder is in the current viewing path
        if (folderPath !== this.currentPath) {
            console.log('[SYNC] Remote mkdir skipped (different path): ' + folderPath + ' != ' + this.currentPath);
            return;
        }
        var f = {
            sha1: data.sha1,
            name: data.name,
            size: 0,
            ext: '',
            is_dir: 1,
            mtime: new Date().toISOString(),
            status: 'synced',
            parent_path: folderPath
        };
        this.fileCache.set(data.sha1, f);
        this.renderFileList(Array.from(this.fileCache.values()));
    },
    
    async deleteFile(sha1) {
        if (!this._isHostAlive()) return;
        if (!this._currentUserHasWritePermission()) {
            VXUI.showMsg(this._t('read_only_permission_denied'), 'error');
            return;
        }
        this.trackUI('sync_delete_file');
        var self = this;
        var file = this.fileCache.get(sha1);
        var fileName = file ? file.name : sha1;
        console.log('[SYNC] Deleting file: ' + fileName + ' sha1=' + sha1);

        // Mark file as deleting (row shows 'deleting' status)
        this._fileStatus.set(sha1, 'deleting');
        this._updateFileRow(sha1);

        // handleRemoteDelete handles both local FS deletion and cache update
        await this.handleRemoteDelete(sha1, this._t('sync_this_device'));

        // Broadcast to all peers
        await this.sendToAllPeers('file_op', {
            action: 'delete',
            sha1: sha1,
            name: fileName
        });
        // Phase 1 (B): local FS changed → push fresh state to peers immediately
        this._triggerImmediateSync('delete');
    },
    
    async createFolder(name) {
        if (!this._isHostAlive()) return;
        if (!this._currentUserHasWritePermission()) {
            VXUI.showMsg(this._t('read_only_permission_denied'), 'error');
            return;
        }
        this.trackUI('sync_create_folder');
        var self = this;
        var parentPath = this.currentPath;
        console.log('[SYNC] Creating folder: ' + name + ' in drive=' + this.currentDrive.drive_id + ' path=' + parentPath);

        // Generate folder metadata locally (server no longer processes file ops).
        var sha1 = await this._fingerprintFile(name, parentPath, 0, '');
        var folderData = {
            sha1: sha1,
            name: name,
            parent_path: parentPath
        };

        // handleRemoteMkdir creates the folder in local FS and updates cache
        await this.handleRemoteMkdir(folderData, '\u672c\u673a');

        // Broadcast to all peers
        await this.sendToAllPeers('file_op', {
            action: 'mkdir',
            name: name,
            parent_path: parentPath,
            sha1: sha1
        });
        this._triggerImmediateSync('mkdir');
    },
    
    async renameFile(sha1, newName) {
        if (!this._isHostAlive()) return;
        if (!this._currentUserHasWritePermission()) {
            VXUI.showMsg(this._t('read_only_permission_denied'), 'error');
            return;
        }
        this.trackUI('sync_rename_file');
        var self = this;
        var file = this.fileCache.get(sha1);
        if (!file) return;
        var oldName = file.name;
        var oldPath = (file.parent_path || '/') + '/' + oldName;
        console.log('[SYNC] Renaming file: ' + oldName + ' -> ' + newName + ' sha1=' + sha1);

        // 1. Rename local FS file
        var ok = await this._renameLocalFile(oldPath, newName);
        if (!ok) {
            console.warn('[SYNC] Local rename failed, aborting sync');
            this.addActivity('rename', oldName + ' \u2192 ' + newName + ' (\u5931\u8d25)', { source: this._t('sync_this_device'), target: this._t('sync_all_peers') });
            return;
        }

        // 2. Update fileCache: remove old sha1, compute new sha1 and add
        this.fileCache.delete(sha1);
        var newSha1 = await this._fingerprintFile(newName, file.parent_path || '/', file.size, file.mtime);
        var newEntry = {
            sha1: newSha1,
            name: newName,
            size: file.size,
            parent_path: file.parent_path || '/',
            mtime: Date.now()
        };
        this.fileCache.set(newSha1, newEntry);

        // 3. Broadcast to all peers
        await this.sendToAllPeers('file_op', {
            action: 'rename',
            sha1: sha1,
            new_sha1: newSha1,
            new_name: newName,
            old_name: oldName,
            parent_path: file.parent_path || '/'
        });

        this.addActivity('rename', oldName + ' \u2192 ' + newName, { source: this._t('sync_this_device'), target: this._t('sync_all_peers') });
        this.renderFileList(Array.from(this.fileCache.values()));

        // Track old path as pending rename — prevents race condition where Peer
        // reports the old path before receiving the file_op rename command
        if (!this._hostPendingOps) this._hostPendingOps = {};
        var newPath = (file.parent_path === '/' ? '' : file.parent_path) + '/' + newName;
        this._hostPendingOps[oldPath] = { op: 'rename', newPath: newPath, ts: Date.now() };

        this._triggerImmediateSync('rename');
    },

    async moveFile(sha1, newParentPath) {
        if (!this._isHostAlive()) return;
        if (!this._currentUserHasWritePermission()) {
            VXUI.showMsg(this._t('read_only_permission_denied'), 'error');
            return;
        }
        this.trackUI('sync_move_file');
        var self = this;
        var file = this.fileCache.get(sha1);
        if (!file) return;
        var oldPath = (file.parent_path || '/') + '/' + file.name;
        console.log('[SYNC] Moving file: ' + file.name + ' sha1=' + sha1 + ' -> ' + newParentPath);

        // 1. Move local FS file
        var ok = await this._moveLocalFile(oldPath, newParentPath);
        if (!ok) {
            console.warn('[SYNC] Local move failed, aborting sync');
            this.addActivity('move', file.name + ' \u2192 ' + newParentPath + ' (\u5931\u8d25)', { source: this._t('sync_this_device'), target: this._t('sync_all_peers') });
            return;
        }

        // 2. Update fileCache: remove old sha1, compute new sha1 and add
        this.fileCache.delete(sha1);
        var newSha1 = await this._fingerprintFile(file.name, newParentPath, file.size, file.mtime);
        var newEntry = {
            sha1: newSha1,
            name: file.name,
            size: file.size,
            parent_path: newParentPath,
            mtime: Date.now()
        };
        this.fileCache.set(newSha1, newEntry);

        // 3. Broadcast to all peers
        await this.sendToAllPeers('file_op', {
            action: 'move',
            sha1: sha1,
            new_sha1: newSha1,
            new_parent_path: newParentPath,
            old_parent_path: file.parent_path || '/',
            name: file.name
        });

        this.addActivity('move', file.name + ' \u2192 ' + newParentPath, { source: this._t('sync_this_device'), target: this._t('sync_all_peers') });
        this.renderFileList(Array.from(this.fileCache.values()));

        // Track old path as pending move — prevents race condition where Peer
        // reports the old path before receiving the file_op move command
        if (!this._hostPendingOps) this._hostPendingOps = {};
        var movedNewPath = (newParentPath === '/' ? '' : newParentPath) + '/' + file.name;
        this._hostPendingOps[oldPath] = { op: 'move', newPath: movedNewPath, ts: Date.now() };

        this._triggerImmediateSync('move');
    },
    
    // ========== Peer List ==========
    updatePeerList() {
        var container = document.getElementById('sync-peer-list');
        if (!container) return;

        var peerCount = this.peers ? this.peers.length : 0;
        console.log('[SYNC] Updating peer list: ' + peerCount + ' peers online');

        var countText = document.getElementById('sync-peer-count-text');
        if (countText) countText.textContent = this._formatPeerQuota(peerCount);

        this.updateStatus();

        if (peerCount === 0) {
            container.innerHTML = '<div class="vx-sync-peer-empty" data-tpl="sync_no_peers">\u6682\u65e0\u5df2\u8fde\u63a5\u8bbe\u5907</div>';
            return;
        }

        var isHost = this.isHost;
        var myUid = this.getMyUidFromCache();

        container.innerHTML = this.peers.map(function(p) {
            var peerId = p.peer_id || 'peer';
            var displayId = peerId.length > 8 ? peerId.substring(0, 8) + '...' : peerId;
            var isMe = (String(myUid) === String(peerId));
            var statusText = '\u5728\u7ebf';
            var meTag = isMe ? ' <span class="vx-sync-peer-tag-me">\u6211</span>' : '';
            // Prefer device_name; fall back to truncated peer_id
            var displayName = (p.device_name && p.device_name.length > 0) ? p.device_name : displayId;

            // Determine connection mode for this peer
            var connMode = '';
            if (VX_SYNC.isHost) {
                // Host: check per-peer connection state
                var conn = VX_SYNC._peerConnections[p.device_id];
                if (conn) {
                    if (conn.mode === 'p2p') connMode = ' <span class="vx-sync-conn-badge mode-p2p">直连</span>';
                    else if (conn.mode === 'relay') connMode = ' <span class="vx-sync-conn-badge mode-relay">中转</span>';
                    else connMode = ' <span class="vx-sync-conn-badge mode-unknown">...</span>';
                }
            } else {
                // Peer: only the Host entry has a direct connection
                // Match host by: role field, peer_id prefix, or device_id matching drive's host_device_id
                var isHostPeer = p.role === 'host' || (peerId && peerId.indexOf('host_') === 0);
                if (!isHostPeer && VX_SYNC.currentDrive && p.device_id === VX_SYNC.currentDrive.host_device_id) {
                    isHostPeer = true;
                }
                if (isHostPeer) {
                    if (VX_SYNC._hostConnectionMode === 'p2p') connMode = ' <span class="vx-sync-conn-badge mode-p2p">直连</span>';
                    else if (VX_SYNC._hostConnectionMode === 'relay') connMode = ' <span class="vx-sync-conn-badge mode-relay">中转</span>';
                    else if (VX_SYNC._hostConnectionMode !== 'unknown') connMode = ' <span class="vx-sync-conn-badge mode-unknown">...</span>';
                }
            }

            return '<div class="vx-list-row">' +
                '<div class="vx-list-name">' +
                    '<div class="vx-list-icon"><iconpark-icon name="user"></iconpark-icon></div>' +
                    '<div class="vx-list-filename"><span>' + VX_SYNC.escapeHtml(displayName) + '</span>' + meTag + connMode + '</div>' +
                '</div>' +
                '<div class="vx-list-date"><span class="vx-text-success">\u25cf ' + statusText + '</span></div>' +
            '</div>';
        }).join('');
    },

    updateStatus(status) {
        if (status) {
            if (this._syncStatus !== status) {
                console.log('[SYNC] Status changed: ' + this._syncStatus + ' -> ' + status);
            }
            this._syncStatus = status;
        }
        var icon = document.getElementById('sync-status-icon');
        var text = document.getElementById('sync-status-text');
        if (!icon || !text) return;

        var statusIcons = {
            idle: 'link-cloud',
            ready: 'link-cloud',
            syncing: 'cloud-arrow-up',
            offline: 'wifi-exclamation'
        };
        icon.setAttribute('name', statusIcons[this._syncStatus] || 'link-cloud');
        icon.className = 'status-' + this._syncStatus;

        var langData = {};
        if (typeof app !== 'undefined' && app && app.languageData) {
            langData = app.languageData;
        }
        var messages = {
            idle: langData['sync_status_idle'] || '未连接',
            ready: langData['sync_status_ready'] || '就绪',
            syncing: langData['sync_status_syncing'] || '同步中...',
            offline: langData['sync_status_offline'] || '离线'
        };
        var peerInfo = '';
        var peerCount = this.peers ? this.peers.length : 0;
        if (this.currentDrive) {
            peerInfo = ' · ' + this._formatPeerQuota(peerCount) + ' ' + (langData['sync_peers_title'] || this._t('sync_peers_title'));
        }
        text.textContent = messages[this._syncStatus] + peerInfo;
        this.updateTransferStats();
    },

    updateTransferStats() {
        var statsFiles = document.getElementById('sync-stats-files');
        var statsData = document.getElementById('sync-stats-data');
        if (!statsFiles || !statsData) return;

        var s = this._transferStats;
        var totalFiles = s.filesUploaded + s.filesDownloaded;
        var totalBytes = s.bytesUploaded + s.bytesDownloaded;
        statsFiles.textContent = String(totalFiles);
        statsData.textContent = this.formatFileSize(totalBytes);
    },

    // ========== Drag & Drop ==========
    setupDragDrop() {
        var self = this;
        var tree = document.getElementById('sync-content-area');
        if (!tree) return;

        ['dragenter', 'dragover', 'dragleave', 'drop'].forEach(function(evt) {
            tree.addEventListener(evt, function(e) {
                e.preventDefault();
                e.stopPropagation();
            });
        });

        var dragCounter = 0;
        tree.addEventListener('dragenter', function(e) {
            dragCounter++;
            tree.classList.add('drag-over');
            self.showDropHint(true);
        });

        tree.addEventListener('dragleave', function(e) {
            dragCounter--;
            if (dragCounter <= 0) {
                dragCounter = 0;
                tree.classList.remove('drag-over');
                self.showDropHint(false);
            }
        });

        tree.addEventListener('drop', function(e) {
            dragCounter = 0;
            tree.classList.remove('drag-over');
            self.showDropHint(false);
            var files = e.dataTransfer.files;
            if (files && files.length > 0) {
                Array.from(files).forEach(function(file) {
                    self.uploadFile(file);
                });
            }
        });
    },

    showDropHint(show) {
        var hint = document.getElementById('sync-drop-hint');
        if (hint) hint.style.display = show ? '' : 'none';
    },

    // ========== Context Menu ==========
    showContextMenu(sha1, name, x, y) {
        if (!this._isHostAlive()) return;
        this._ctxTarget = { sha1: sha1, name: name };
        var menu = document.getElementById('sync-context-menu');
        if (!menu) return;

        // Hide download option for folders, show open instead
        var file = this.fileCache.get(sha1);
        var isDir = file && (file.is_dir == 1 || file.is_dir === true);
        var dlItem = menu.querySelector('.vx-ctx-download');
        var openItem = menu.querySelector('.vx-ctx-open');
        if (isDir) {
            if (dlItem) dlItem.style.display = 'none';
            if (openItem) openItem.style.display = '';
        } else {
            if (dlItem) dlItem.style.display = '';
            if (openItem) openItem.style.display = 'none';
        }

        menu.style.display = '';
        menu.style.left = x + 'px';
        menu.style.top = y + 'px';

        var self = this;
        var closeCtx = function() {
            self.hideContextMenu();
            document.removeEventListener('click', closeCtx);
            document.removeEventListener('contextmenu', closeCtx);
        };
        setTimeout(function() {
            document.addEventListener('click', closeCtx);
            document.addEventListener('contextmenu', closeCtx);
        }, 0);
    },

    hideContextMenu() {
        var menu = document.getElementById('sync-context-menu');
        if (menu) menu.style.display = 'none';
        this._ctxTarget = null;
    },

    ctxDownload() {
        if (this._ctxTarget) this.downloadFile(this._ctxTarget.sha1);
        this.hideContextMenu();
    },

    ctxOpen() {
        if (this._ctxTarget) this.openFolder(this._ctxTarget.sha1, this._ctxTarget.name);
        this.hideContextMenu();
    },

    ctxRename() {
        if (!this._ctxTarget) return;
        var sha1 = this._ctxTarget.sha1;
        var oldName = this._ctxTarget.name;
        this.hideContextMenu();
        var newName = prompt('Rename:', oldName);
        if (newName && newName !== oldName) {
            this.renameFile(sha1, newName);
        }
    },

    ctxShare() {
        if (!this._ctxTarget) return;
        this.trackUI('sync_share_link');
        this.hideContextMenu();
        var link = window.location.origin + '/vx?module=sync&drive=' +
            (this.currentDrive ? this.currentDrive.drive_id : '');
        navigator.clipboard.writeText(link).then(function() {
            VX_SYNC.toastSuccess(VX_SYNC._t('sync_link_copied'));
        });
    },

    ctxDelete() {
        if (!this._ctxTarget) return;
        var sha1 = this._ctxTarget.sha1;
        this.hideContextMenu();
        if (confirm('Delete this file?')) {
            this.deleteFile(sha1);
        }
    },

    // ========== Folder Navigation ==========
    openFolder(sha1, name) {
        this.trackUI('sync_open_folder');
        var newPath;
        if (this.currentPath === '/') {
            newPath = '/' + name;
        } else {
            newPath = this.currentPath + '/' + name;
        }
        console.log('[SYNC] Opening folder: ' + name + ' -> path=' + newPath);
        this.listFiles(newPath);
    },

    navigateToPath(path) {
        if (!path) path = '/';
        console.log('[SYNC] Navigating to path: ' + path);
        this.listFiles(path);
    },

    goBack() {
        if (this.currentPath === '/' || !this.currentPath) return;
        this.trackUI('sync_go_back');
        var parts = this.currentPath.split('/').filter(function(p) { return p; });
        parts.pop();
        var parentPath = parts.length === 0 ? '/' : '/' + parts.join('/');
        console.log('[SYNC] Going back to: ' + parentPath);
        this.listFiles(parentPath);
    },

    updateBreadcrumb() {
        var bcEl = document.getElementById('sync-path-breadcrumb');
        if (!bcEl) return;

        var driveName = (this.currentDrive ? (this.currentDrive.drive_name || this.currentDrive.name || '同步盘') : '');
        // First crumb: back to drive list; second crumb: drive root
        var html = '<a href="javascript:;" onclick="VX_SYNC.leaveDrive()"><span data-tpl="sync_title">文件同步盘</span></a>' +
            '<span class="vx-breadcrumb-sep">/</span>' +
            '<a href="javascript:;" onclick="VX_SYNC.navigateToPath(\'/\')">' + this.escapeHtml(driveName) + '</a>';

        if (this.currentPath && this.currentPath !== '/') {
            var parts = this.currentPath.split('/').filter(function(p) { return p; });
            var accumulated = '';
            for (var i = 0; i < parts.length; i++) {
                accumulated += '/' + parts[i];
                html += '<span class="vx-breadcrumb-sep">/</span>';
                if (i < parts.length - 1) {
                    html += '<a href="javascript:;" onclick="VX_SYNC.navigateToPath(\'' + accumulated + '\')">' + this.escapeHtml(parts[i]) + '</a>';
                } else {
                    html += '<span>' + this.escapeHtml(parts[i]) + '</span>';
                }
            }
        }

        bcEl.innerHTML = html;

        // Show/hide back button based on current path
        var backBtn = document.getElementById('sync-btn-go-back');
        var backSep = document.getElementById('sync-btn-go-back-sep');
        var showBack = (this.currentPath && this.currentPath !== '/');
        if (backBtn) {
            backBtn.style.display = showBack ? '' : 'none';
        }
        if (backSep) {
            backSep.style.display = showBack ? '' : 'none';
        }
    },

    // ========== Folder Binding ==========
    async selectFolder() {
        this.trackUI('sync_select_folder');
        console.log('[SYNC] Opening folder picker...');
        try {
            var dirHandle = await window.showDirectoryPicker({ mode: 'readwrite' });
            this._boundFolder = {
                name: dirHandle.name,
                handle: dirHandle
            };

            // 多 session：同步写入当前 session，并获取文件夹锁文件（物理排他）
            var session = this._getActiveSession();
            if (session) {
                session.boundFolder = this._boundFolder;
                var locked = await this._acquireFolderLock(session);
                if (!locked) {
                    VXUI.showMsg(this._t('sync_folder_locked_other_tab'), 'warning');
                    this._boundFolder = null;
                    session.boundFolder = null;
                    this._updateFolderPathDisplay();
                    this.showLobby();
                    return;
                }
                this._bcast('drive_locked', {
                    drive_id: session.drive_id,
                    role: session.role,
                    folder_name: session.boundFolder.name
                });
            }

            console.log('[SYNC] Folder bound: ' + dirHandle.name);
            this._updateFolderPathDisplay();
            this.addActivity('bind_folder', dirHandle.name);
            this.toastSuccess(this._t('sync_folder_bound').replace('{name}', dirHandle.name));
            if (this.currentDrive && this.currentDrive.drive_id) {
                this._saveFolderHandle(dirHandle, this.currentDrive.drive_id);
            }
            // Phase 2 (A): begin native FS observation (no-op if unsupported).
            // stopPeriodicSync() is NOT called here, so if an observer from a
            // previous folder is still active, _startFSObserver stops it first
            // via _stopFSObserver to avoid leaking the old handle.
            this._stopFSObserver();
            this._startFSObserver();
            // Phase 2.5: pre-check FileSystemObserver support. Browsers without
            // native file watching (Chrome <133, Edge <133, Opera <118, Safari,
            // Firefox) fall back to polling only, so warn the user once that
            // sync real-time performance may be reduced.
            if (!this._fsObserverSupported) {
                var warned = false;
                try {
                    warned = localStorage.getItem('vx_sync_fs_observer_warned') === '1';
                    if (!warned) {
                        localStorage.setItem('vx_sync_fs_observer_warned', '1');
                    }
                } catch (e) { /* localStorage may be unavailable */ }
                if (!warned) {
                    this.toastWarning(this._t('sync_fs_observer_unavailable'));
                }
            }
            // Load persisted sync state from .tmpsync/state.json
            await this._loadSyncState();
            // Trigger bidirectional sync if DataChannel is already open
            if (!this.isHost) {
                var dc = this.acceptDC;
                if (dc && dc.readyState === 'open') {
                    console.log('[SYNC] Peer folder bound after DC open, sending file report (folder_changed=true)');
                    // Pass folderChanged=true so Host does not mistake missing
                    // files for deletions on this first report.
                    this.sendPeerFileReport(true);
                }
            } else {
                // Host: re-list files and send to all connected Peers, then request fresh peer_file_report
                var hasOpenPeer = Object.keys(this._peerConnections).some(function(pid) {
                    var pdc = VX_SYNC._peerConnections[pid].dc;
                    return pdc && pdc.readyState === 'open';
                });
                if (hasOpenPeer) {
                    var hostSelf = this;
                    this._listDirectoryAt(this.currentPath).then(function(files) {
                        hostSelf.sendToAllPeers('file_list_resp', { files: files, path: hostSelf.currentPath });
                    });
                    // Request Peer to re-send its file report for delta calculation
                    this.sendToAllPeers('file_report_req', {});
                }
            }
        } catch (e) {
            if (e.name === 'AbortError') {
                console.log('[SYNC] Folder picker cancelled by user');
            } else {
                console.error('[SYNC] Folder selection error:', e);
                this.toastError(this._t('sync_select_folder_failed'));
            }
        }
    },

    _updateFolderPathDisplay() {
        var path = this._boundFolder ? this._boundFolder.name : '';

        var detailPath = document.getElementById('sync-detail-folder-path');
        if (detailPath) {
            if (path) {
                detailPath.removeAttribute('data-tpl');
                detailPath.textContent = path;
            } else {
                detailPath.setAttribute('data-tpl', 'sync_no_folder_selected');
                detailPath.textContent = '\u672a\u9009\u62e9\u6587\u4ef6\u5939';
            }
        }

        var changeBtn = document.querySelector('.vx-sync-change-folder-btn');
        if (changeBtn) {
            changeBtn.style.display = path ? '' : 'none';
        }
    },

    // Allow changing the bound folder while in an active drive (after P2P connection).
    async changeBoundFolder() {
        this.trackUI('sync_change_folder');

        // If no folder currently bound, just use selectFolder directly
        if (!this._boundFolder || !this._boundFolder.handle) {
            await this.selectFolder();
            return;
        }

        console.log('[SYNC] Changing bound folder...');

        // Stop current FS observer to avoid leaking handles
        this._stopFSObserver();

        // Prompt user for new folder
        try {
            var dirHandle = await window.showDirectoryPicker({ mode: 'readwrite' });
        } catch (e) {
            if (e.name === 'AbortError') {
                console.log('[SYNC] Folder change cancelled by user');
            } else {
                console.error('[SYNC] Folder selection error:', e);
                this.toastError(this._t('sync_select_folder_failed'));
            }
            return;
        }

        // Update bound folder reference
        this._boundFolder = {
            name: dirHandle.name,
            handle: dirHandle
        };
        console.log('[SYNC] Folder changed to: ' + dirHandle.name);

        // Save new binding to IndexedDB
        if (this.currentDrive && this.currentDrive.drive_id) {
            await this._saveFolderHandle(dirHandle, this.currentDrive.drive_id);
        }

        // Update UI and activity log
        this._updateFolderPathDisplay();
        this.addActivity('change_folder', dirHandle.name);
        this.toastSuccess(this._t('sync_folder_bound').replace('{name}', dirHandle.name));

        // Reset Peer-side last-sync state before loading the new folder's
        // state. The old _peerLastPaths belongs to the previous folder and
        // must NOT leak into the new folder's sync — otherwise every file
        // from the old folder would be reported as "deleted", and Host would
        // propagate those phantom deletions to itself, wiping Host's files.
        if (!this.isHost) {
            this._peerLastPaths = null;
        }

        // Load persisted sync state from .tmpsync/state.json in new folder
        await this._loadSyncState();

        // Phase 2 (A): start FS observer on new folder
        this._startFSObserver();

        // Trigger bidirectional sync if DataChannel is already open
        if (!this.isHost) {
            var dc = this.acceptDC;
            if (dc && dc.readyState === 'open') {
                console.log('[SYNC] Peer folder changed after DC open, sending file report (folder_changed=true)');
                this.sendPeerFileReport(true);
            }
        } else {
            // Host: re-list files and send to all connected Peers, then request fresh peer_file_report
            var hostSelf = this;
            var hasOpenPeer = Object.keys(this._peerConnections).some(function(pid) {
                var pdc = VX_SYNC._peerConnections[pid].dc;
                return pdc && pdc.readyState === 'open';
            });
            if (hasOpenPeer) {
                this._listDirectoryAt(this.currentPath).then(function(files) {
                    hostSelf.sendToAllPeers('file_list_resp', { files: files, path: hostSelf.currentPath });
                });
                // Request Peer to re-send its file report for delta calculation
                this.sendToAllPeers('file_report_req', {});
            }
        }
    },

    getBoundFolderFiles() {
        if (!this._boundFolder || !this._boundFolder.handle) return [];
        var self = this;
        return this._readDirectoryRecursive(this._boundFolder.handle, '/');
    },

    // Traverse from bound root to get directory handle at a specific path
    async _getDirectoryHandle(path) {
        if (!this._boundFolder || !this._boundFolder.handle) return null;
        if (!path || path === '/') return this._boundFolder.handle;

        var parts = path.split('/').filter(function(p) { return p; });
        var handle = this._boundFolder.handle;
        for (var i = 0; i < parts.length; i++) {
            try {
                handle = await handle.getDirectoryHandle(parts[i]);
            } catch (e) {
                console.warn('[SYNC] Directory not found: ' + parts[i] + ' in path ' + path);
                return null;
            }
        }
        return handle;
    },

    // List immediate children at a specific path (non-recursive, real-time)
    async _listDirectoryAt(path) {
        var dirHandle = await this._getDirectoryHandle(path);
        if (!dirHandle) {
            console.warn('[SYNC] Cannot list directory: no handle for path=' + path);
            return [];
        }

        var items = [];
        for await (var [name, handle] of dirHandle.entries()) {
            if (name === '.tmpsync') continue;
            if (this._isIgnoredEntry(name, handle.kind === 'directory')) continue;
            if (handle.kind === 'file') {
                var file = await handle.getFile();
                var sha1 = await this._fingerprintFile(name, path, file.size, new Date(file.lastModified).toISOString());
                items.push({
                    name: name,
                    size: file.size,
                    mtime: new Date(file.lastModified).toISOString(),
                    is_dir: 0,
                    parent_path: path,
                    sha1: sha1
                });
            } else if (handle.kind === 'directory') {
                items.push({
                    name: name,
                    size: 0,
                    mtime: new Date().toISOString(),
                    is_dir: 1,
                    parent_path: path,
                    sha1: 'dir_' + path + '/' + name
                });
            }
        }
        // Sort: folders first, then files, alphabetically
        items.sort(function(a, b) {
            if (a.is_dir !== b.is_dir) return b.is_dir - a.is_dir;
            return a.name.localeCompare(b.name);
        });
        return items;
    },

    // Read a file's binary content directly from the bound folder (Host only)
    async getFileFromFileSystem(sha1) {
        if (!this._boundFolder || !this._boundFolder.handle) return null;
        
        // Look up file metadata from cache to get name and parent_path
        var meta = this.fileCache.get(sha1);
        
        // Fallback: if not in cache, scan the bound folder to find the file by sha1
        if (!meta) {
            console.log('[SYNC] getFileFromFileSystem: sha1 not in cache, scanning folder: ' + sha1);
            try {
                var allFiles = await this.getBoundFolderFiles();
                for (var i = 0; i < allFiles.length; i++) {
                    var f = allFiles[i];
                    if (f.is_dir) continue;
                    var computedSha1 = await this._fingerprintFile(f.name, f.parent_path, f.size, f.mtime);
                    if (computedSha1 === sha1) {
                        meta = { name: f.name, parent_path: f.parent_path, size: f.size, mtime: f.mtime };
                        // Cache it for future use
                        this.fileCache.set(sha1, Object.assign({ sha1: sha1 }, meta));
                        console.log('[SYNC] getFileFromFileSystem: found via scan: ' + meta.name + ' at ' + meta.parent_path);
                        break;
                    }
                }
            } catch (e) {
                console.warn('[SYNC] getFileFromFileSystem fallback scan failed:', e);
            }
        }
        
        if (!meta) {
            console.warn('[SYNC] getFileFromFileSystem: file not found for sha1=' + sha1);
            return null;
        }
        
        try {
            var dirHandle = await this._getDirectoryHandle(meta.parent_path || '/');
            if (!dirHandle) return null;
            var fileHandle = await dirHandle.getFileHandle(meta.name);
            var file = await fileHandle.getFile();
            console.log('[SYNC] Read file from filesystem: ' + meta.name + ' size=' + file.size);
            return { blob: file, name: meta.name, size: file.size };
        } catch (e) {
            console.warn('[SYNC] getFileFromFileSystem failed for ' + meta.name + ':', e);
            return null;
        }
    },

    // Trigger browser download (for manual downloads or fallback)
    _triggerBrowserDownload(blob, fileName) {
        var url = URL.createObjectURL(blob);
        var a = document.createElement('a');
        a.href = url;
        a.download = fileName;
        document.body.appendChild(a);
        a.click();
        document.body.removeChild(a);
        URL.revokeObjectURL(url);
    },

    // Write a received file to the local bound folder (bidirectional sync, Host and Peer)
    async _writeFileToLocalFolder(meta, blob) {
        if (!this._boundFolder || !this._boundFolder.handle) {
            console.warn('[SYNC] _writeFileToLocalFolder: no bound folder');
            return false;
        }

        try {
            // Navigate to (or create) the target directory
            var dirHandle = this._boundFolder.handle;
            var parentPath = meta.parent_path || '/';
            if (parentPath && parentPath !== '/') {
                var parts = parentPath.split('/').filter(function(p) { return p; });
                for (var i = 0; i < parts.length; i++) {
                    dirHandle = await dirHandle.getDirectoryHandle(parts[i], { create: true });
                }
            }

            // Create or overwrite the file
            var fileHandle = await dirHandle.getFileHandle(meta.name, { create: true });
            var writable = await fileHandle.createWritable();
            await writable.write(blob);
            await writable.close();

            console.log('[SYNC] File written to local folder: ' + meta.name + ' at ' + parentPath + ' size=' + blob.size);
            return true;
        } catch (e) {
            console.error('[SYNC] _writeFileToLocalFolder failed for ' + meta.name + ':', e);
            return false;
        }
    },

    // Delete a file from the local bound folder (used for deletion propagation)
    async _deleteLocalFile(parentPath, fileName) {
        if (!this._boundFolder || !this._boundFolder.handle) {
            console.warn('[SYNC] _deleteLocalFile: no bound folder');
            return false;
        }

        try {
            var dirHandle = this._boundFolder.handle;
            if (parentPath && parentPath !== '/') {
                var parts = parentPath.split('/').filter(function(p) { return p; });
                for (var i = 0; i < parts.length; i++) {
                    dirHandle = await dirHandle.getDirectoryHandle(parts[i], { create: false });
                }
            }
            await dirHandle.removeEntry(fileName);
            console.log('[SYNC] Deleted local file: ' + fileName + ' at ' + parentPath);
            return true;
        } catch (e) {
            console.warn('[SYNC] _deleteLocalFile failed for ' + fileName + ' at ' + parentPath + ':', e);
            return false;
        }
    },

    // Rename a local file: copy content to new name, then delete old file.
    // File System Access API has no direct rename method.
    async _renameLocalFile(oldPath, newName) {
        if (!this._boundFolder || !this._boundFolder.handle) return false;
        try {
            var oldName = oldPath.split('/').pop();
            var dirPath = oldPath.substring(0, oldPath.lastIndexOf('/') + 1);
            var dirHandle = await this._getDirectoryHandle(dirPath);
            if (!dirHandle) return false;

            var oldFileHandle = await dirHandle.getFileHandle(oldName, { create: false });
            var file = await oldFileHandle.getFile();
            var blob = file.slice(0, file.size, file.type);

            var newFileHandle = await dirHandle.getFileHandle(newName, { create: true });
            var writable = await newFileHandle.createWritable();
            await writable.write(blob);
            await writable.close();

            await dirHandle.removeEntry(oldName);
            console.log('[SYNC] Renamed local file: ' + oldPath + ' -> ' + newName);
            return true;
        } catch (e) {
            console.error('[SYNC] Failed to rename local file ' + oldPath + ':', e);
            return false;
        }
    },

    // Move a local file to a different directory.
    async _moveLocalFile(oldPath, newParentPath) {
        if (!this._boundFolder || !this._boundFolder.handle) return false;
        try {
            var oldName = oldPath.split('/').pop();
            var oldDirPath = oldPath.substring(0, oldPath.lastIndexOf('/') + 1);
            var oldDirHandle = await this._getDirectoryHandle(oldDirPath);
            if (!oldDirHandle) return false;

            var oldFileHandle = await oldDirHandle.getFileHandle(oldName, { create: false });
            var file = await oldFileHandle.getFile();
            var blob = file.slice(0, file.size, file.type);

            var newDirHandle = await this._getDirectoryHandle(newParentPath);
            if (!newDirHandle) return false;

            var newFileHandle = await newDirHandle.getFileHandle(oldName, { create: true });
            var writable = await newFileHandle.createWritable();
            await writable.write(blob);
            await writable.close();

            await oldDirHandle.removeEntry(oldName);
            console.log('[SYNC] Moved local file: ' + oldPath + ' -> ' + newParentPath + '/' + oldName);
            return true;
        } catch (e) {
            console.error('[SYNC] Failed to move local file ' + oldPath + ':', e);
            return false;
        }
    },

    async _createLocalFolder(parentPath, folderName) {
        if (!this._boundFolder || !this._boundFolder.handle) return false;
        try {
            var parentHandle = await this._getDirectoryHandle(parentPath);
            if (!parentHandle) return false;
            await parentHandle.getDirectoryHandle(folderName, { create: true });
            console.log('[SYNC] Created local folder: ' + folderName + ' at ' + parentPath);
            return true;
        } catch (e) {
            console.warn('[SYNC] _createLocalFolder failed for "' + folderName + '" at ' + parentPath + ':', e);
            return false;
        }
    },

    // ========== Folder Lock File ==========
    // .tmpsync/drive.lock 实现物理文件夹排他性。
    // 同一磁盘文件夹无论被哪个浏览器、哪个 tab 绑定，都会读取到同一个锁文件。
    // 心跳每 1s 更新一次，3s 未更新视为同步盘不处于运行状态，可被覆盖。
    _LOCK_FILE_NAME: 'drive.lock',
    _LOCK_HEARTBEAT_INTERVAL_MS: 1000,    // 心跳间隔 1s（运行状态指示）
    _LOCK_EXPIRE_MS: 3000,                // 锁过期阈值 3s

    // 生成随机 nonce（用于写入后读回校验，防并发覆盖）
    _generateLockNonce() {
        return Math.random().toString(36).substring(2, 12) + Date.now().toString(36);
    },

    // 读取锁文件内容。返回 null 表示不存在或读取失败。
    async _readDriveLockFile(folderHandle) {
        if (!folderHandle) return null;
        try {
            var tmpDir = await folderHandle.getDirectoryHandle('.tmpsync', { create: false });
            var fileHandle;
            try {
                fileHandle = await tmpDir.getFileHandle(this._LOCK_FILE_NAME, { create: false });
            } catch (e) {
                return null; // 锁文件不存在
            }
            var file = await fileHandle.getFile();
            var text = await file.text();
            return JSON.parse(text);
        } catch (e) {
            return null;
        }
    },

    // 写入锁文件（覆盖式）。
    async _writeDriveLockFile(folderHandle, lockData) {
        if (!folderHandle) return false;
        try {
            var tmpDir = await folderHandle.getDirectoryHandle('.tmpsync', { create: true });
            var fileHandle = await tmpDir.getFileHandle(this._LOCK_FILE_NAME, { create: true });
            var writable = await fileHandle.createWritable();
            await writable.write(JSON.stringify(lockData, null, 2));
            await writable.close();
            return true;
        } catch (e) {
            console.warn('[SYNC] Failed to write drive.lock:', e);
            return false;
        }
    },

    // 删除锁文件。
    async _deleteDriveLockFile(folderHandle) {
        if (!folderHandle) return;
        try {
            var tmpDir = await folderHandle.getDirectoryHandle('.tmpsync', { create: false });
            await tmpDir.removeEntry(this._LOCK_FILE_NAME);
        } catch (e) {
            // 文件不存在或删除失败，忽略
        }
    },

    // 校验锁文件是否过期
    _isLockExpired(lockData) {
        if (!lockData || !lockData.last_heartbeat) return true;
        var lastHB = new Date(lockData.last_heartbeat).getTime();
        if (isNaN(lastHB)) return true;
        return (Date.now() - lastHB) > this._LOCK_EXPIRE_MS;
    },

    // 尝试占用文件夹锁。返回 true 表示成功，false 表示冲突。
    async _acquireFolderLock(session) {
        if (!session || !session.boundFolder || !session.boundFolder.handle) return true;
        var folderHandle = session.boundFolder.handle;
        var nonce = this._generateLockNonce();

        // 1. 读取现有锁文件
        var existing = await this._readDriveLockFile(folderHandle);
        if (existing) {
            var isOwn = (existing.tab_id === this._tabID &&
                         existing.device_id === this.getDeviceId() &&
                         existing.uid === TL.uid);
            var isExpired = this._isLockExpired(existing);

            if (!isOwn && !isExpired) {
                // 锁属于其它 tab/device 且未过期 → 冲突
                console.warn('[SYNC] Folder locked by another session:', existing);
                return false;
            }
            // isOwn 或 isExpired → 可以覆盖
        }

        // 2. 写入新锁文件
        var now = new Date().toISOString();
        var lockData = {
            drive_id: session.drive_id,
            uid: TL.uid,
            device_id: this.getDeviceId(),
            tab_id: this._tabID,
            role: session.role,
            nonce: nonce,
            locked_at: existing ? existing.locked_at : now,
            last_heartbeat: now
        };
        var written = await this._writeDriveLockFile(folderHandle, lockData);
        if (!written) return false;

        // 3. 立即读回，校验 nonce（防并发覆盖）
        var readback = await this._readDriveLockFile(folderHandle);
        if (!readback || readback.nonce !== nonce) {
            console.warn('[SYNC] Folder lock nonce mismatch, concurrent acquisition detected');
            return false;
        }

        session.lockNonce = nonce;
        console.log('[SYNC] Folder lock acquired for drive ' + session.drive_id + ' nonce=' + nonce);
        return true;
    },

    // 更新锁文件 heartbeat（每 1s 定时调用，作为同步盘运行状态指示）。
    async _touchDriveLockFile(session) {
        if (!session || !session.boundFolder || !session.boundFolder.handle) return;
        if (!session.lockNonce) return; // 未持有锁
        var folderHandle = session.boundFolder.handle;

        // 读取当前锁，确认仍属于本 session
        var current = await this._readDriveLockFile(folderHandle);
        if (!current || current.nonce !== session.lockNonce) {
            // 锁已被其它 session 覆盖，清除本地 nonce
            console.warn('[SYNC] Folder lock lost (nonce mismatch) for drive ' + session.drive_id);
            session.lockNonce = null;
            return;
        }

        // 更新 heartbeat
        current.last_heartbeat = new Date().toISOString();
        await this._writeDriveLockFile(folderHandle, current);
    },

    // 释放文件夹锁（leaveDrive / 页面卸载时调用）。
    async _releaseFolderLock(session) {
        if (!session || !session.boundFolder || !session.boundFolder.handle) return;
        if (!session.lockNonce) return;
        var folderHandle = session.boundFolder.handle;

        // 确认锁仍属于本 session 再删除
        var current = await this._readDriveLockFile(folderHandle);
        if (current && current.nonce === session.lockNonce) {
            await this._deleteDriveLockFile(folderHandle);
            console.log('[SYNC] Folder lock released for drive ' + session.drive_id);
        }
        session.lockNonce = null;
    },

    // ========== .tmpsync State Persistence ==========
    // The .tmpsync directory stores sync state (file path tracking, etc.)
    // It is excluded from sync scanning and never transferred between nodes.

    // Get or create the .tmpsync directory handle inside the bound folder
    async _getTmpSyncDir() {
        if (!this._boundFolder || !this._boundFolder.handle) return null;
        try {
            return await this._boundFolder.handle.getDirectoryHandle('.tmpsync', { create: true });
        } catch (e) {
            console.warn('[SYNC] Failed to get/create .tmpsync dir:', e);
            return null;
        }
    },

    // Save sync state to .tmpsync/state.json
    async _saveSyncState() {
        if (!this._boundFolder || !this._boundFolder.handle) return;
        try {
            var tmpDir = await this._getTmpSyncDir();
            if (!tmpDir) return;

            var state = {
                version: 2,
                device_id: this.deviceId || '',
                is_host: this.isHost,
                drive_id: this.currentDrive ? this.currentDrive.drive_id : null,
                saved_at: new Date().toISOString(),
                last_sync_paths: {
                    local: this.isHost ? this._hostLastPaths : this._peerLastPaths,
                    remote: this.isHost ? this._peerLastPaths : null
                },
                host_pending_ops: this.isHost ? (this._hostPendingOps || null) : null
            };

            var fileHandle = await tmpDir.getFileHandle('state.json', { create: true });
            var writable = await fileHandle.createWritable();
            await writable.write(JSON.stringify(state, null, 2));
            await writable.close();
            console.log('[SYNC] State saved to .tmpsync/state.json (local=' + Object.keys(state.last_sync_paths.local || {}).length + ' paths)');
        } catch (e) {
            console.warn('[SYNC] Failed to save sync state:', e);
        }
    },

    // Load sync state from .tmpsync/state.json
    async _loadSyncState() {
        if (!this._boundFolder || !this._boundFolder.handle) return;
        try {
            var tmpDir = await this._getTmpSyncDir();
            if (!tmpDir) return;

            var fileHandle;
            try {
                fileHandle = await tmpDir.getFileHandle('state.json', { create: false });
            } catch (e) {
                console.log('[SYNC] No .tmpsync/state.json found, starting fresh');
                return;
            }

            var file = await fileHandle.getFile();
            var text = await file.text();
            var state = JSON.parse(text);

            if (state.version !== 1 && state.version !== 2) {
                console.log('[SYNC] State version mismatch (v' + state.version + '), ignoring stored state');
                return;
            }

            // Restore last-known paths based on role
            if (this.isHost) {
                this._hostLastPaths = state.last_sync_paths.local || null;
                this._peerLastPaths = state.last_sync_paths.remote || null;
                // Restore pending Host operations (v2+)
                this._hostPendingOps = state.host_pending_ops || null;
            } else {
                this._peerLastPaths = state.last_sync_paths.local || null;
            }

            var localCount = Object.keys(state.last_sync_paths.local || {}).length;
            var remoteCount = Object.keys(state.last_sync_paths.remote || {}).length;
            console.log('[SYNC] State loaded from .tmpsync/state.json (local=' + localCount + ' remote=' + remoteCount + ' paths, saved_at=' + state.saved_at + ')');
        } catch (e) {
            console.warn('[SYNC] Failed to load sync state:', e);
        }
    },

    // Clear sync state (called when leaving or deleting a drive)
    async _clearSyncState() {
        if (!this._boundFolder || !this._boundFolder.handle) return;
        try {
            var tmpDir = await this._getTmpSyncDir();
            if (!tmpDir) return;
            // Remove the state.json file
            await tmpDir.removeEntry('state.json').catch(function() {});
            console.log('[SYNC] Cleared .tmpsync/state.json');
        } catch (e) {
            console.warn('[SYNC] Failed to clear sync state:', e);
        }
    },

    async _readDirectoryRecursive(dirHandle, relativePath) {
        var files = [];
        for await (var [name, handle] of dirHandle.entries()) {
            if (name === '.tmpsync') continue;
            if (this._isIgnoredEntry(name, handle.kind === 'directory')) continue;
            if (handle.kind === 'file') {
                var file = await handle.getFile();
                files.push({
                    name: name,
                    handle: handle,
                    path: relativePath === '/' ? '/' + name : relativePath + '/' + name,
                    parent_path: relativePath,
                    size: file.size,
                    mtime: new Date(file.lastModified).toISOString(),
                    is_dir: 0
                });
            } else if (handle.kind === 'directory') {
                var dirPath = relativePath === '/' ? '/' + name : relativePath + '/' + name;
                files.push({
                    name: name,
                    handle: handle,
                    path: dirPath,
                    parent_path: relativePath,
                    size: 0,
                    mtime: new Date().toISOString(),
                    is_dir: 1
                });
                var subFiles = await this._readDirectoryRecursive(handle, dirPath);
                files = files.concat(subFiles);
            }
        }
        return files;
    },

    // ========== Folder Scanning & Indexing ==========

    // Check if a file or directory should be excluded from sync.
    // Files: .DS_Store (macOS Finder metadata), ._* (AppleDouble resource fork),
    //   .crswap / .crdownload (Chrome temp downloads), .tmp (generic temp files),
    //   Thumbs.db (Windows thumbnail cache), .localized (macOS folder localization)
    // Directories: .Spotlight-V100, .Trashes, .fseventsd, .TemporaryItems
    _isIgnoredEntry(name, isDir) {
        if (!name) return false;
        if (isDir) {
            return name === '.Spotlight-V100' || name === '.Trashes' ||
                   name === '.fseventsd' || name === '.TemporaryItems';
        }
        // Files: system metadata + temp files
        if (name === '.DS_Store' || name === '.localized' || name === 'Thumbs.db') return true;
        if (name.startsWith('._')) return true;
        var lower = name.toLowerCase();
        return lower.endsWith('.crswap') || lower.endsWith('.crdownload') || lower.endsWith('.tmp');
    },

    async _fingerprintFile(name, parentPath, size, mtime) {
        // Use path+name+size as fingerprint (NOT mtime).
        // mtime differs between Host and Peer after sync (write time != original time),
        // which would cause infinite re-sync loops. Path+size is stable across nodes.
        var str = (parentPath === '/' ? '' : parentPath) + '/' + name + '|' + size;
        var encoder = new TextEncoder();
        var data = encoder.encode(str);
        var hashBuffer = await crypto.subtle.digest('SHA-1', data);
        var hashArray = Array.from(new Uint8Array(hashBuffer));
        return hashArray.map(function(b) { return b.toString(16).padStart(2, '0'); }).join('');
    },

    // ========== Permission Helpers ==========

    // Check if the current user is the owner of the given drive (or currentDrive).
    _isDriveOwner(drive) {
        drive = drive || this.currentDrive;
        if (!drive) return false;
        return String(drive.host_uid) === String(TL.uid);
    },

    // Host or drive owner can manage permissions (invite codes, join requests).
    _canManagePermissions() {
        return this.isHost || this._isDriveOwner();
    },

    // ========== Activity Tracking ==========

    /**
     * 记录 UI 行为（event_ui）
     * @param {string} title
     */
    trackUI(title) {
        try {
            if (!title) return;
            if (typeof TL !== 'undefined' && TL && typeof TL.ga === 'function') {
                TL.ga(title);
            }
        } catch (e) {
            // ignore
        }
    },

    addActivity(type, desc, details) {
        var activity = {
            type: type,
            desc: desc || '',
            time: new Date().toISOString(),
            details: details || null
        };
        console.log('[SYNC] Activity: [' + type + '] ' + desc + (details ? ' ' + JSON.stringify(details) : ''));
        this._activities.unshift(activity);
        if (this._activities.length > 300) {
            this._activities = this._activities.slice(0, 300);
        }
        this.renderActivityList();
    },

    // Build HTML for activity metadata line (source → target + mode badge).
    // details: { source, target, mode } — any field may be omitted.
    _renderActivityMeta(details) {
        if (!details) return '';
        var parts = [];
        if (details.source || details.target) {
            var src = details.source || '—';
            var tgt = details.target || '—';
            parts.push('<span>' + this.escapeHtml(src) + ' \u2192 ' + this.escapeHtml(tgt) + '</span>');
        }
        if (details.mode === 'p2p') {
            parts.push('<span class="vx-sync-conn-badge mode-p2p">' + this._t('sync_mode_p2p') + '</span>');
        } else if (details.mode === 'relay') {
            parts.push('<span class="vx-sync-conn-badge mode-relay">' + this._t('sync_mode_relay') + '</span>');
        }
        if (parts.length === 0) return '';
        return '<div class="vx-sync-activity-meta">' + parts.join('') + '</div>';
    },

    // Update (or create) a transfer activity with progress, speed, mode, source.
    // Only re-renders the specific DOM element to avoid full list redraw on every chunk.
    upsertTransferActivity(type, fileName, sha1, progress, speed, mode, sourceNode) {
        var id = 'transfer_' + sha1;
        var now = new Date().toISOString();
        // Find existing activity by id
        var existing = null;
        for (var i = 0; i < this._activities.length; i++) {
            if (this._activities[i].id === id) { existing = this._activities[i]; break; }
        }
        if (existing) {
            existing.desc = fileName;
            existing.time = now;
            existing.progress = progress;
            existing.speed = speed;
            existing.mode = mode;
            existing.source = sourceNode;
        } else {
            var activity = {
                id: id,
                type: type,
                desc: fileName,
                time: now,
                progress: progress,
                speed: speed,
                mode: mode,
                source: sourceNode
            };
            this._activities.unshift(activity);
            if (this._activities.length > 300) {
                this._activities = this._activities.slice(0, 300);
            }
        }
        // Update just the DOM element for this transfer
        this._renderTransferActivity(id, type, fileName, progress, speed, mode, sourceNode);
    },

    _renderTransferActivity(id, type, fileName, progress, speed, mode, sourceNode) {
        var detailContainer = document.getElementById('sync-detail-activity-items');
        if (!detailContainer) return;

        var icon = type === 'download' ? '\u2b07\ufe0f' : '\u2b06\ufe0f';
        var pct = Math.min(100, Math.max(0, Math.round(progress)));
        var pctText = pct + '%';
        var speedText = speed || '';
        var modeBadge = '';
        if (mode === 'p2p') {
            modeBadge = '<span class="vx-sync-conn-badge mode-p2p">' + VX_SYNC._t('sync_mode_p2p') + '</span>';
        } else if (mode === 'relay') {
            modeBadge = '<span class="vx-sync-conn-badge mode-relay">' + VX_SYNC._t('sync_mode_relay') + '</span>';
        }
        // Build source → target text: download = sourceNode → 本机, upload = 本机 → sourceNode
        var thisDevice = VX_SYNC._t('sync_this_device');
        var routeText = '';
        if (sourceNode) {
            if (type === 'download') {
                routeText = '<span class="vx-text-muted">' + VX_SYNC.escapeHtml(sourceNode) + ' \u2192 ' + VX_SYNC.escapeHtml(thisDevice) + '</span>';
            } else {
                routeText = '<span class="vx-text-muted">' + VX_SYNC.escapeHtml(thisDevice) + ' \u2192 ' + VX_SYNC.escapeHtml(sourceNode) + '</span>';
            }
        }

        var html = '<div class="vx-list-row vx-sync-transfer-row" data-transfer-id="' + id + '" data-transfer-type="' + type + '">' +
            '<div class="vx-list-name">' +
                '<div class="vx-list-icon"><span class="vx-sync-activity-icon">' + icon + '</span></div>' +
                '<div class="vx-list-filename">' +
                    '<span>' + VX_SYNC.escapeHtml(fileName) + '</span>' +
                    '<div class="vx-sync-transfer-bar"><div class="vx-sync-transfer-fill" style="width:' + pct + '%"></div></div>' +
                    '<div class="vx-sync-transfer-info">' +
                        '<span class="vx-text-muted">' + pctText + '</span>' +
                        (speedText ? ' &middot; <span class="vx-text-muted">' + speedText + '</span>' : '') +
                        modeBadge +
                        (routeText ? ' | ' + routeText : '') +
                    '</div>' +
                '</div>' +
            '</div>' +
        '</div>';

        // Check if this element already exists in the DOM
        var existingEl = detailContainer.querySelector('[data-transfer-id="' + id + '"]');
        if (existingEl) {
            existingEl.outerHTML = html;
        } else {
            // Prepend to the activity list
            var firstChild = detailContainer.firstChild;
            if (firstChild) {
                detailContainer.insertAdjacentHTML('afterbegin', html);
            } else {
                detailContainer.innerHTML = html;
            }
        }
    },

    _removeTransferActivity(sha1) {
        var id = 'transfer_' + sha1;
        // Remove from the activities array
        for (var i = this._activities.length - 1; i >= 0; i--) {
            if (this._activities[i].id === id) { this._activities.splice(i, 1); break; }
        }
        // Remove from DOM
        var el = document.getElementById('sync-detail-activity-items');
        if (el) {
            var transferEl = el.querySelector('[data-transfer-id="' + id + '"]');
            if (transferEl) transferEl.remove();
        }
    },

    renderActivityList() {
        var detailContainer = document.getElementById('sync-detail-activity-items');
        if (!detailContainer) return;

        // Filter out transfer activities (they're rendered independently via upsertTransferActivity)
        var nonTransfer = this._activities.filter(function(a) { return !a.id || a.id.indexOf('transfer_') !== 0; });

        if (nonTransfer.length === 0 && !detailContainer.querySelector('[data-transfer-id]')) {
            detailContainer.innerHTML = '<div class="vx-sync-activity-empty" data-tpl="sync_no_activity">\u6682\u65e0\u6d3b\u52a8</div>';
            return;
        }

        // Build HTML for non-transfer activities only
        var html = nonTransfer.map(function(a) {
            var timeStr = VX_SYNC.formatDateTime(a.time);
            var icon = VX_SYNC._getActivityIcon(a.type);
            var metaHtml = VX_SYNC._renderActivityMeta(a.details);
            return '<div class="vx-list-row">' +
                '<div class="vx-list-name">' +
                    '<div class="vx-list-icon"><span class="vx-sync-activity-icon">' + icon + '</span></div>' +
                    '<div class="vx-list-filename">' +
                        '<span>' + VX_SYNC.escapeHtml(a.desc) + '</span>' +
                        metaHtml +
                    '</div>' +
                '</div>' +
                '<div class="vx-list-date"><span class="vx-text-muted">' + timeStr + '</span></div>' +
            '</div>';
        }).join('');

        // Append transfer items that are in the data but not yet in the DOM
        var transferItems = this._activities.filter(function(a) { return a.id && a.id.indexOf('transfer_') === 0; });
        for (var i = 0; i < transferItems.length; i++) {
            var t = transferItems[i];
            if (!detailContainer.querySelector('[data-transfer-id="' + t.id + '"]')) {
                var tModeBadge = '';
                if (t.mode === 'p2p') {
                    tModeBadge = '<span class="vx-sync-conn-badge mode-p2p">' + VX_SYNC._t('sync_mode_p2p') + '</span>';
                } else if (t.mode === 'relay') {
                    tModeBadge = '<span class="vx-sync-conn-badge mode-relay">' + VX_SYNC._t('sync_mode_relay') + '</span>';
                }
                var tRoute = '';
                if (t.source) {
                    var tDev = VX_SYNC._t('sync_this_device');
                    if (t.type === 'download') {
                        tRoute = '<span class="vx-text-muted">' + VX_SYNC.escapeHtml(t.source) + ' \u2192 ' + VX_SYNC.escapeHtml(tDev) + '</span>';
                    } else {
                        tRoute = '<span class="vx-text-muted">' + VX_SYNC.escapeHtml(tDev) + ' \u2192 ' + VX_SYNC.escapeHtml(t.source) + '</span>';
                    }
                }
                html = '<div class="vx-list-row vx-sync-transfer-row" data-transfer-id="' + t.id + '" data-transfer-type="' + t.type + '">' +
                    '<div class="vx-list-name">' +
                        '<div class="vx-list-icon"><span class="vx-sync-activity-icon">' + (t.type === 'download' ? '\u2b07\ufe0f' : '\u2b06\ufe0f') + '</span></div>' +
                        '<div class="vx-list-filename">' +
                            '<span>' + VX_SYNC.escapeHtml(t.desc) + '</span>' +
                            '<div class="vx-sync-transfer-bar"><div class="vx-sync-transfer-fill" style="width:' + (t.progress || 0) + '%"></div></div>' +
                            '<div class="vx-sync-transfer-info"><span class="vx-text-muted">' + (t.progress || 0) + '%</span>' + tModeBadge + (tRoute ? ' | ' + tRoute : '') + '</div>' +
                        '</div>' +
                    '</div>' +
                '</div>' + html;
            }
        }

        // Preserve existing transfer DOM elements while replacing non-transfer content
        var transferEls = detailContainer.querySelectorAll('[data-transfer-id]');
        var transferHTML = '';
        transferEls.forEach(function(el) { transferHTML += el.outerHTML; });
        detailContainer.innerHTML = transferHTML + html;
    },

    _getActivityIcon(type) {
        var icons = {
            'create_drive': '\ud83d\udcc1',
            'start_server': '\ud83d\udfe2',
            'connect_host': '\ud83d\udd17',
            'bind_folder': '\ud83d\udcc2',
            'change_folder': '\ud83d\udd04',
            'upload': '\u2b06\ufe0f',
            'download': '\u2b07\ufe0f',
            'delete': '\ud83d\uddd1\ufe0f',
            'rename': '\u270f\ufe0f',
            'create_folder': '\ud83d\udcc1',
            'peer_join': '\ud83d\udc65',
            'peer_leave': '\ud83d\udce4',
            'sync_complete': '\u2705',
            'conflict': '\u26a0\ufe0f',
            'p2p_connected': '\ud83c\udf10',
            'sync_push': '\ud83d\udce4',
            'sync_pull': '\ud83d\udce5',
            'sync_upload': '\u2b06\ufe0f',
            'sync_received': '\u2b07\ufe0f',
            'sync_delta': '\ud83d\udd04',
            'drive_delete': '\ud83d\uddd1\ufe0f',
            'drive_leave': '\ud83d\udce4'
        };
        return icons[type] || '\ud83d\udccc';
    },

    _formatSpeed(bytesPerSec) {
        if (!bytesPerSec || bytesPerSec <= 0) return '';
        if (bytesPerSec >= 1024 * 1024) {
            return (bytesPerSec / (1024 * 1024)).toFixed(1) + ' MB/s';
        } else if (bytesPerSec >= 1024) {
            return (bytesPerSec / 1024).toFixed(1) + ' KB/s';
        }
        return Math.round(bytesPerSec) + ' B/s';
    },

    // ========== Phase 8.5: Latency & Multi-Source ==========
    pingPeer(targetUid) {
        var self = this;
        return new Promise(function(resolve) {
            var start = Date.now();
            var timeoutId = setTimeout(function() {
                resolve(9999);
            }, 5000);
            
            var handler = function(e) {
                var msg = JSON.parse(e.data);
                if (msg.type === 'latency_pong' && msg.data) {
                    var d = msg.data;
                    if (typeof d === 'string') d = JSON.parse(d);
                    if (d.target_uid == targetUid) {
                        clearTimeout(timeoutId);
                        var rtt = Date.now() - start;
                        var latency = Math.round(rtt / 2);
                        resolve(latency);
                        self.signalingWS.removeEventListener('message', handler);
                    }
                }
            };
            self.signalingWS.addEventListener('message', handler);
            
            self.sendSignaling({
                type: 'latency_ping',
                data: JSON.stringify({ target_uid: targetUid, timestamp: start })
            });
        });
    },
    
    async startLatencyMeasure(peerList) {
        var self = this;
        var myUid = this.getMyUid();
        if (!myUid) return;
        
        for (var i = 0; i < peerList.length; i++) {
            var p = peerList[i];
            if (p.uid == myUid) continue;
            var latency = await this.pingPeer(p.uid);
            if (latency < 9999) {
                this.sendSignaling({
                    type: 'latency_report',
                    data: JSON.stringify({
                        from_uid: String(myUid),
                        to_uid: String(p.uid),
                        latency_ms: latency
                    })
                });
            }
        }
    },
    
    getMyUid() {
        if (this.peers && this.peers.length > 0) {
            for (var i = 0; i < this.peers.length; i++) {
                if (this.peers[i].peer_id === null) continue;
            }
        }
        return null;
    },
    
    async reportFileAvailability() {
        if (!this.currentDrive || !this._boundFolder || !this._boundFolder.handle) return;
        
        var files = [];
        try {
            var allFiles = await this.getBoundFolderFiles();
            for (var i = 0; i < allFiles.length; i++) {
                var f = allFiles[i];
                if (f.is_dir) continue;
                var sha1 = await this._fingerprintFile(f.name, f.path, f.size, f.mtime);
                files.push({ sha1: sha1, name: f.name, size: f.size, mtime: f.mtime });
            }
        } catch (e) {
            console.warn('[SYNC] reportFileAvailability failed:', e);
        }
        
        var myUid = this.getMyUidFromCache();
        if (!myUid) return;
        
        console.log('[SYNC] Reporting file availability: ' + files.length + ' files for uid=' + myUid);
        this.sendSignaling({
            type: 'file_availability',
            data: JSON.stringify({ peer_uid: String(myUid), files: files })
        });
    },
    
    getMyUidFromCache() {
        var uid = null;
        if (typeof TL !== 'undefined' && TL.uid) {
            uid = TL.uid;
        }
        return uid;
    },
    
    async multiSourceDownload(sha1) {
        var self = this;
        
        this.sendSignaling({
            type: 'file_download_query',
            data: JSON.stringify({ sha1: sha1 })
        });
        
        var candidates = await this.waitForCandidates(sha1);
        if (!candidates || candidates.length === 0) {
            console.log('[SYNC] No download candidates for ' + sha1 + ', falling back to Host');
            this.sendToDC({ t: 'file_download_req', d: { sha1: sha1 } });
            return;
        }
        
        var best = candidates[0];
        console.log('[SYNC] Downloading ' + sha1 + ' from: uid=' + best.uid + ' is_authority=' + best.is_authority + ' latency=' + (best.latency || 'N/A') + 'ms candidates=' + candidates.length);
        
        if (best.is_authority) {
            this.sendToDC({ t: 'file_download_req', d: { sha1: sha1 } });
        } else {
            this.sendSignaling({
                type: 'file_download_req',
                target_uid: parseInt(best.uid),
                data: JSON.stringify({ sha1: sha1 })
            });
        }
    },
    
    waitForCandidates(sha1) {
        var self = this;
        return new Promise(function(resolve) {
            var timeoutId = setTimeout(function() { resolve(null); }, 3000);
            
            var handler = function(e) {
                var msg = JSON.parse(e.data);
                if (msg.type === 'file_download_candidates' && msg.data) {
                    var d = msg.data;
                    if (typeof d === 'string') d = JSON.parse(d);
                    if (d.sha1 === sha1) {
                        clearTimeout(timeoutId);
                        resolve(d.candidates || []);
                        self.signalingWS.removeEventListener('message', handler);
                    }
                }
            };
            self.signalingWS.addEventListener('message', handler);
        });
    },
    
    setupPeerDataChannels(eligibleUIDs) {
        var self = this;
        var myUid = String(this.getMyUidFromCache() || '');
        if (!myUid) return;

        var iceServers = this._getIceServers();
        
        eligibleUIDs.forEach(function(targetUid) {
            targetUid = String(targetUid);
            if (targetUid === myUid) return;
            if (self._peerCons[targetUid]) return;
            
            var pc = new RTCPeerConnection({
                iceServers: iceServers,
                iceTransportPolicy: 'all'
            });
            
            pc.onicecandidate = function(e) {
                if (e.candidate) {
                    self.sendSignaling({
                        type: 'ice_candidate',
                        target_uid: parseInt(targetUid),
                        candidate: e.candidate
                    });
                }
            };
            
            pc.ondatachannel = function(e) {
                var dc = e.channel;
                self._setupPeerDC(targetUid, dc);
            };
            
            var dc = pc.createDataChannel('peer_sync_' + targetUid, { ordered: true });
            self._peerCons[targetUid] = { pc: pc, dc: dc, pending: true };
            
            pc.createOffer().then(function(offer) {
                return pc.setLocalDescription(offer);
            }).then(function() {
                self.sendSignaling({
                    type: 'offer',
                    target_uid: parseInt(targetUid),
                    sdp: pc.localDescription
                });
            });
            
            console.log('[SYNC] Establishing DC with peer uid=' + targetUid);
        });
    },
    
    _setupPeerDC(targetUid, dc) {
        var self = this;
        dc.binaryType = 'arraybuffer';
        
        dc.onopen = function() {
            console.log('[SYNC] Peer DC opened with uid=' + targetUid + ' label=' + dc.label);
            if (self._peerCons[targetUid]) {
                self._peerCons[targetUid].pending = false;
                self._peerCons[targetUid].dc = dc;
            }
        };
        
        dc.onmessage = function(e) {
            if (typeof e.data === 'string') {
                var msg = JSON.parse(e.data);
                if (msg.t === 'file_download_req') {
                    self.sendFileChunkToDC(dc, msg.d.sha1);
                }
            } else {
                self.handleFileChunk(new Uint8Array(e.data), dc);
            }
        };
        
        dc.onclose = function() {
            console.log('[SYNC] Peer DC closed with uid=' + targetUid);
            delete self._peerCons[targetUid];
        };
        
        if (self._peerCons[targetUid]) {
            self._peerCons[targetUid].dc = dc;
        }
    },
    
    async sendFileChunkToDC(dc, sha1) {
        // Host: read file from bound folder, send to peer DC
        var file = await this.getFileFromFileSystem(sha1);
        if (!file || !dc || dc.readyState !== 'open') {
            console.warn('[SYNC] sendFileChunkToDC: file=' + !!file + ' dc=' + (dc ? dc.readyState : 'null') + ' sha1=' + sha1);
            return;
        }
        
        // Send metadata first
        var meta = this.fileCache.get(sha1);
        var startMeta = { sha1: sha1, name: file.name, size: file.size, sync: true };
        if (meta && meta.parent_path) {
            startMeta.parent_path = meta.parent_path;
        }
        if (dc.readyState === 'open') {
            dc.send(JSON.stringify({ t: 'file_upload_start', d: startMeta }));
        }

        var CHUNK_SIZE = this.CHUNK_SIZE;
        var totalChunks = Math.ceil(file.size / CHUNK_SIZE);
        var BUFFER_THRESHOLD = 4 * 1024 * 1024; // 4MB backpressure threshold
        var blob = file.blob;

        console.log('[SYNC] Sending ' + totalChunks + ' chunks to peer DC: ' + (file.name || sha1));

        for (var i = 0; i < totalChunks; i++) {
            var start = i * CHUNK_SIZE;
            var end = Math.min(start + CHUNK_SIZE, file.size);
            var chunk = blob.slice(start, end);
            var buffer = await chunk.arrayBuffer();
            
            if (dc.readyState !== 'open') {
                console.warn('[SYNC] DC closed during chunk send at ' + (i + 1) + '/' + totalChunks + ' for ' + sha1);
                return;
            }
            
            // Event-based backpressure: wait for buffer to drain if needed
            var ok = await this._waitForBufferDrain(dc, BUFFER_THRESHOLD);
            if (!ok) {
                console.warn('[SYNC] DC closed during backpressure at chunk ' + (i + 1) + '/' + totalChunks + ' for ' + sha1);
                return;
            }
            
            dc.send(buffer);
            if ((i + 1) % 10 === 0 || i === totalChunks - 1) {
                console.log('[SYNC] Sent chunk ' + (i + 1) + '/' + totalChunks + ' for ' + sha1);
            }
        }

        // Wait for buffer to flush before signaling completion
        await this._waitForBufferDrain(dc, 0);
        if (dc.readyState === 'open') {
            dc.send(JSON.stringify({ t: 'file_upload_done', d: { sha1: sha1 } }));
        }
        console.log('[SYNC] All chunks sent to peer DC for ' + sha1);
    },
    
    handlePeerDownloadRequest(msg) {
        var targetUid = msg.target_uid;
        if (!targetUid) return;
        
        var cons = this._peerCons[String(targetUid)];
        if (!cons || !cons.dc || cons.dc.readyState !== 'open') {
            console.warn('[SYNC] handlePeerDownloadRequest: no open DC for uid=' + targetUid);
            return;
        }
        
        var d = msg.data;
        if (typeof d === 'string') d = JSON.parse(d);
        console.log('[SYNC] Peer download request from uid=' + targetUid + ' for sha1=' + d.sha1);
        this.sendFileChunkToDC(cons.dc, d.sha1);
    },
    
    handlePeerOffer(fromUid, msg) {
        var self = this;
        var uid = String(fromUid);
        console.log('[SYNC] Handling peer offer from uid=' + uid);

        var iceServers = this._getIceServers();
        
        var pc = new RTCPeerConnection({
            iceServers: iceServers,
            iceTransportPolicy: 'all'
        });
        
        pc.onicecandidate = function(e) {
            if (e.candidate) {
                self.sendSignaling({
                    type: 'ice_candidate',
                    target_uid: parseInt(uid),
                    candidate: e.candidate
                });
            }
        };
        
        pc.ondatachannel = function(e) {
            var dc = e.channel;
            self._setupPeerDC(uid, dc);
        };
        
        self._peerCons[uid] = { pc: pc, dc: null, pending: true };
        
        pc.setRemoteDescription(new RTCSessionDescription(msg.sdp))
            .then(function() { return pc.createAnswer(); })
            .then(function(answer) { return pc.setLocalDescription(answer); })
            .then(function() {
                console.log('[SYNC] Sending peer answer to uid=' + uid);
                self.sendSignaling({
                    type: 'answer',
                    target_uid: parseInt(uid),
                    sdp: pc.localDescription,
                    data: JSON.stringify({ from_uid: self.getMyUidFromCache() })
                });
            });
        
        console.log('[SYNC] Accepting DC from peer uid=' + uid);
    },
    
    // ========== Loading Overlay ==========
    showLoading(text, subText, progress) {
        // Cancel any pending hide animation if a new loading is shown
        if (this._hideLoadingTimer) { clearTimeout(this._hideLoadingTimer); this._hideLoadingTimer = null; }
        this._loadingCount++;
        var overlay = document.getElementById('sync-loading-overlay');
        var loadingText = document.getElementById('sync-loading-text');
        if (overlay && this._loadingCount === 1) {
            if (loadingText && text) {
                loadingText.textContent = text;
            }
            this._updateLoadingSubText(subText);
            // Reset progress bar to 0% instantly (no transition) before
            // setting the initial progress value, so it never animates backward.
            this._resetProgressBarInstant();
            this._updateLoadingProgressBar(progress);
            overlay.style.display = 'flex';
        }
    },

    // Update the loading progress bar and sub-text without changing the title.
    // Used for multi-step connection flows to show fine-grained progress.
    updateLoadingProgress(text, subText, progress) {
        var loadingText = document.getElementById('sync-loading-text');
        if (loadingText && text) {
            loadingText.textContent = text;
        }
        this._updateLoadingSubText(subText);
        this._updateLoadingProgressBar(progress);
    },

    _updateLoadingSubText(subText) {
        var sub = document.getElementById('sync-loading-sub');
        if (sub) {
            sub.textContent = subText || '';
        }
    },

    _updateLoadingProgressBar(progress) {
        var fill = document.getElementById('sync-loading-fill');
        if (fill) {
            fill.style.width = (progress != null ? Math.min(100, Math.max(0, progress)) : 0) + '%';
        }
    },

    // Reset the progress bar to 0% instantly without any CSS transition.
    // Used when starting a new loading sequence so the bar never animates
    // backward from a previous value.
    _resetProgressBarInstant() {
        var fill = document.getElementById('sync-loading-fill');
        if (!fill) return;
        var orig = fill.style.transition;
        fill.style.transition = 'none';
        fill.style.width = '0%';
        // Force reflow so the browser applies the zero-width before
        // restoring the transition (otherwise the zero-width is skipped).
        fill.offsetHeight;
        fill.style.transition = orig;
    },

    hideLoading() {
        this._loadingCount = Math.max(0, this._loadingCount - 1);
        if (this._loadingCount === 0) {
            var overlay = document.getElementById('sync-loading-overlay');
            if (!overlay) return;

            // Fill the progress bar to 100% with a smooth transition,
            // then wait 1s so the user can see the completion state.
            this._updateLoadingSubText('完成');
            this._updateLoadingProgressBar(100);

            var self = this;
            if (this._hideLoadingTimer) clearTimeout(this._hideLoadingTimer);
            this._hideLoadingTimer = setTimeout(function() {
                self._hideLoadingTimer = null;
                overlay.style.display = 'none';
                // Reset progress bar for next use (instant, no animation)
                self._resetProgressBarInstant();
            }, 1000);
        }
    },

    // ========== Utility Methods ==========
    escapeHtml(text) {
        const div = document.createElement('div');
        div.textContent = text || '';
        return div.innerHTML;
    },
    
    formatFileSize(bytes) {
        if (!bytes) return '0 B';
        const sizes = ['B', 'KB', 'MB', 'GB', 'TB'];
        const i = Math.floor(Math.log(bytes) / Math.log(1024));
        return parseFloat((bytes / Math.pow(1024, i)).toFixed(1)) + ' ' + sizes[i];
    },
    
    formatDate(timestamp) {
        if (!timestamp) return '';
        const date = new Date(timestamp);
        const now = new Date();
        const diff = now - date;
        
        var langData = {};
        if (typeof app !== 'undefined' && app && app.languageData) {
            langData = app.languageData;
        }
        
        if (diff < 60000) return langData['sync_time_just_now'] || '刚刚';
        if (diff < 3600000) return Math.floor(diff / 60000) + (langData['sync_time_minutes_ago'] || ' 分钟前');
        if (diff < 86400000) return Math.floor(diff / 3600000) + (langData['sync_time_hours_ago'] || ' 小时前');
        
        var locale = 'zh-CN';
        if (typeof app !== 'undefined' && app && typeof app.languageGet === 'function') {
            var lang = app.languageGet();
            if (lang === 'en') locale = 'en-US';
            else if (lang === 'ja') locale = 'ja-JP';
        }
        return date.toLocaleDateString(locale);
    },

    // Format a timestamp as a specific date+time (e.g. "2026-07-07 14:30").
    // Used for activity list where relative time is not precise enough.
    formatDateTime(timestamp) {
        if (!timestamp) return '';
        var date = new Date(timestamp);
        var locale = 'zh-CN';
        if (typeof app !== 'undefined' && app && typeof app.languageGet === 'function') {
            var lang = app.languageGet();
            if (lang === 'en') locale = 'en-US';
            else if (lang === 'ja') locale = 'ja-JP';
        }
        try {
            return date.toLocaleString(locale, {
                year: 'numeric',
                month: '2-digit',
                day: '2-digit',
                hour: '2-digit',
                minute: '2-digit'
            });
        } catch (e) {
            return date.toLocaleString();
        }
    },
    
    getFileIcon(filename) {
        const ext = (filename || '').split('.').pop().toLowerCase();
        const iconMap = {
            'pdf': 'file-pdf', 'doc': 'file-word', 'docx': 'file-word',
            'xls': 'file-excel', 'xlsx': 'file-excel', 'ppt': 'file-powerpoint',
            'jpg': 'file-image', 'jpeg': 'file-image', 'png': 'file-image', 'gif': 'file-image',
            'mp4': 'file-video', 'mkv': 'file-video', 'avi': 'file-video',
            'mp3': 'file-music', 'wav': 'file-music', 'flac': 'file-music',
            'zip': 'file-zipper', 'rar': 'file-zipper', '7z': 'file-zipper'
        };
        return iconMap[ext] || 'file';
    },
    
    ensureLanguageReady() {
        if (typeof VXUI !== 'undefined' && VXUI) {
            return VXUI.ensureLanguageReady();
        }
        return Promise.resolve();
    },
    
    toastSuccess(msg) {
        if (typeof VXUI !== 'undefined' && VXUI && typeof VXUI.toastSuccess === 'function') {
            VXUI.toastSuccess(msg);
        }
    },
    
    toastError(msg) {
        if (typeof VXUI !== 'undefined' && VXUI && typeof VXUI.toastError === 'function') {
            VXUI.toastError(msg);
        }
    },
    
    toastWarning(msg) {
        if (typeof VXUI !== 'undefined' && VXUI && typeof VXUI.toastWarning === 'function') {
            VXUI.toastWarning(msg);
        }
    },

    toastInfo(msg) {
        if (typeof VXUI !== 'undefined' && VXUI && typeof VXUI.toastInfo === 'function') {
            VXUI.toastInfo(msg);
        }
    },

    // ========== Invite Code Operations ==========

    showGenerateInviteCode() {
        this.trackUI('sync_show_generate_invite');
        document.getElementById('sync-generate-invite-modal').style.display = 'flex';
        // Bind custom input visibility
        var self = this;
        ['invite_expires', 'max_uses', 'perm_expires'].forEach(function(name) {
            document.querySelectorAll('input[name="' + name + '"]').forEach(function(radio) {
                radio.onchange = function() {
                    var customId = '';
                    if (name === 'invite_expires') customId = 'invite-expires-custom';
                    else if (name === 'max_uses') customId = 'max-uses-custom';
                    else customId = 'perm-expires-custom';
                    var customInput = document.getElementById(customId);
                    if (customInput) {
                        customInput.style.display = this.value === 'custom' ? 'block' : 'none';
                    }
                };
            });
        });
    },

    hideGenerateInviteCode() {
        document.getElementById('sync-generate-invite-modal').style.display = 'none';
    },

    async doGenerateInviteCode() {
        var getSelectedValue = function(name) {
            var checked = document.querySelector('input[name="' + name + '"]:checked');
            if (!checked) return 0;
            return parseInt(checked.value) || 0;
        };

        // Handle custom values
        var expiresDays = getSelectedValue('invite_expires');
        if (document.querySelector('input[name="invite_expires"]:checked') &&
            document.querySelector('input[name="invite_expires"]:checked').value === 'custom') {
            var custom = parseInt(document.getElementById('invite-expires-custom').value);
            expiresDays = isNaN(custom) ? 0 : custom;
        }

        var maxUses = getSelectedValue('max_uses');
        if (document.querySelector('input[name="max_uses"]:checked') &&
            document.querySelector('input[name="max_uses"]:checked').value === 'custom') {
            var custom = parseInt(document.getElementById('max-uses-custom').value);
            maxUses = isNaN(custom) ? 0 : custom;
        }

        var permExpiresDays = getSelectedValue('perm_expires');
        if (document.querySelector('input[name="perm_expires"]:checked') &&
            document.querySelector('input[name="perm_expires"]:checked').value === 'custom') {
            var custom = parseInt(document.getElementById('perm-expires-custom').value);
            permExpiresDays = isNaN(custom) ? 0 : custom;
        }

        var permissionEl = document.querySelector('input[name="permission"]:checked');
        var permission = permissionEl ? permissionEl.value : 'read';

        try {
            var resp = await this.wsRequest('invite_code_create_req', {
                drive_id: this.currentDrive.drive_id,
                permission: permission,
                expires_days: expiresDays,
                max_uses: maxUses,
                permission_expires_days: permExpiresDays,
            });
            if (resp.status !== 1) return;
            VXUI.showMsg(this._t('sync_invite_created'), 'success');
            this.hideGenerateInviteCode();
            this.loadInviteCodes();
        } catch (e) {
            console.error('generate invite code failed', e);
            VXUI.showMsg('生成失败，请重试', 'error');
        }
    },

    async loadInviteCodes() {
        if (!this.currentDrive || !this._canManagePermissions()) return;

        try {
            var resp = await this.wsRequest('invite_code_list_req', {
                drive_id: this.currentDrive.drive_id,
            });
            if (resp.status !== 1) return;
            this._inviteCodes = (resp.data && resp.data.codes) || [];
            this.renderInviteCodeList();
        } catch (e) {
            console.error('loadInviteCodes error', e);
        }
    },

    renderInviteCodeList() {
        var container = document.getElementById('sync-invite-code-list');
        if (!this._inviteCodes || this._inviteCodes.length === 0) {
            container.innerHTML = '<tr class="vx-sync-empty-row"><td colspan="6" data-tpl="sync_no_invite_codes">暂无邀请码</td></tr>';
            if (typeof VXUI !== 'undefined' && VXUI.translateContainer) VXUI.translateContainer(container);
            return;
        }

        var html = '';
        var self = this;
        this._inviteCodes.forEach(function(code) {
            var isExpired = code.expires_at && new Date(code.expires_at) < new Date();
            var statusClass = code.status === 'active' && !isExpired ? 'active' : 'revoked';
            var statusText = code.status === 'active' && !isExpired
                ? self._t('sync_active')
                : self._t('sync_revoked');
            var permLabel = code.permission === 'read'
                ? self._t('sync_permission_read')
                : self._t('sync_permission_write');
            var permClass = code.permission === 'read' ? 'read' : 'read-write';
            var expiresText = code.expires_days === 0
                ? self._t('sync_expires_unlimited')
                : (code.expires_at || '-');

            html += '<tr>' +
                '<td><span class="vx-sync-invite-code">' + self.escapeHtml(code.invite_code) + '</span></td>' +
                '<td><span class="vx-sync-permission-badge ' + permClass + '">' + permLabel + '</span></td>' +
                '<td>' + code.used_count + (code.max_uses > 0 ? '/' + code.max_uses : '') + '</td>' +
                '<td>' + (isExpired ? '<span class="vx-sync-expired">' + expiresText + '</span>' : expiresText) + '</td>' +
                '<td><span class="vx-sync-status-badge ' + statusClass + '">' + statusText + '</span></td>' +
                '<td>' +
                    (code.status === 'active'
                        ? '<button class="vx-btn vx-btn-danger vx-btn-xs vx-sync-btn-xs" onclick="VX_SYNC.revokeInviteCode(' + code.id + ')">' + self._t('sync_revoke') + '</button>'
                        : '') +
                '</td>' +
            '</tr>';
        });
        container.innerHTML = html;
    },

    async revokeInviteCode(codeId) {
        if (!confirm(this._t('sync_revoke_invite_confirm'))) return;

        try {
            var resp = await this.wsRequest('invite_code_revoke_req', {
                drive_id: this.currentDrive.drive_id,
                code_id: codeId,
            });
            if (resp.status !== 1) return;
            VXUI.showMsg(this._t('sync_invite_revoked'), 'success');
            this.loadInviteCodes();
        } catch (e) {
            console.error('revoke failed', e);
            VXUI.showMsg('撤销失败，请重试', 'error');
        }
    },

    // ========== Join Request Operations ==========

    async loadJoinRequests() {
        if (!this.currentDrive || !this._canManagePermissions()) return;

        try {
            var resp = await this.wsRequest('join_request_list_req', {
                drive_id: this.currentDrive.drive_id,
            });
            if (resp.status !== 1) return;
            this._joinRequests = (resp.data && resp.data.requests) || [];
            this.renderJoinRequestList();
        } catch (e) {
            console.error('loadJoinRequests error', e);
        }
    },

    renderJoinRequestList() {
        var container = document.getElementById('sync-join-request-list');
        if (!this._joinRequests || this._joinRequests.length === 0) {
            container.innerHTML = '<tr class="vx-sync-empty-row"><td colspan="6" data-tpl="sync_no_requests">暂无申请</td></tr>';
            if (typeof VXUI !== 'undefined' && VXUI.translateContainer) VXUI.translateContainer(container);
            return;
        }

        var html = '';
        var self = this;
        this._joinRequests.forEach(function(req) {
            var permLabel = req.permission === 'read'
                ? self._t('sync_permission_read')
                : self._t('sync_permission_write');
            var permClass = req.permission === 'read' ? 'read' : 'read-write';
            var statusClass = req.status;
            var statusText = self._t('sync_' + req.status);
            var expiresText = req.expires_at || self._t('sync_expires_unlimited');

            html += '<tr>' +
                '<td>' + self.escapeHtml(req.applicant_name || '#' + req.applicant_uid) + '</td>' +
                '<td><span class="vx-sync-permission-badge ' + permClass + '">' + permLabel + '</span></td>' +
                '<td>' + expiresText + '</td>' +
                '<td><span class="vx-sync-status-badge ' + statusClass + '">' + statusText + '</span></td>' +
                '<td>' + req.created_at + '</td>' +
                '<td>' +
                    (req.status === 'pending'
                        ? '<button class="vx-btn vx-btn-primary vx-btn-xs vx-sync-btn-xs" onclick="VX_SYNC.approveJoinRequest(' + req.id + ')">' + self._t('sync_approve') + '</button> ' +
                          '<button class="vx-btn vx-btn-danger vx-btn-xs vx-sync-btn-xs" onclick="VX_SYNC.rejectJoinRequest(' + req.id + ')">' + self._t('sync_reject') + '</button>'
                        : req.status === 'approved'
                        ? '<button class="vx-btn vx-btn-danger vx-btn-xs vx-sync-btn-xs" onclick="VX_SYNC.revokeJoinRequest(' + req.id + ')">' + self._t('sync_revoke') + '</button>'
                        : '') +
                '</td>' +
            '</tr>';
        });
        container.innerHTML = html;
        if (typeof VXUI !== 'undefined' && VXUI.translateContainer) VXUI.translateContainer(container);
    },

    async approveJoinRequest(requestId) {
        try {
            var resp = await this.wsRequest('join_request_approve', {
                drive_id: this.currentDrive.drive_id,
                request_id: requestId,
            });
            if (resp.status !== 1) return;
            VXUI.showMsg(this._t('sync_request_approved'), 'success');
            this.loadJoinRequests();
        } catch (e) {
            console.error('approve failed', e);
            VXUI.showMsg('批准失败，请重试', 'error');
        }
    },

    async rejectJoinRequest(requestId) {
        if (!confirm(this._t('sync_reject_confirm'))) return;
        try {
            var resp = await this.wsRequest('join_request_reject', {
                drive_id: this.currentDrive.drive_id,
                request_id: requestId,
            });
            if (resp.status !== 1) return;
            VXUI.showMsg(this._t('sync_request_rejected'), 'success');
            this.loadJoinRequests();
        } catch (e) {
            console.error('reject failed', e);
            VXUI.showMsg('拒绝失败，请重试', 'error');
        }
    },

    async revokeJoinRequest(requestId) {
        if (!confirm(this._t('sync_revoke_permission_confirm'))) return;
        try {
            var resp = await this.wsRequest('join_request_revoke', {
                drive_id: this.currentDrive.drive_id,
                request_id: requestId,
            });
            if (resp.status !== 1) return;
            VXUI.showMsg(this._t('sync_permission_revoked'), 'success');
            this.loadJoinRequests();
        } catch (e) {
            console.error('revoke failed', e);
            VXUI.showMsg('撤销失败，请重试', 'error');
        }
    },

    // ========== Notification Operations ==========

    async loadNotifications() {
        try {
            var resp = await this.wsRequest('notification_list_req', {});
            if (resp.status !== 1) return;
            this._notifications = (resp.data && resp.data.notifications) || [];
            // Sync unread count with actual unread items in the list
            var unreadInList = 0;
            this._notifications.forEach(function(n) { if (!n.is_read) unreadInList++; });
            this._unreadNotificationCount = unreadInList;
            this.renderNotifications();
            this.updateUnreadBadge();
        } catch (e) {
            console.error('loadNotifications error', e);
        }
    },

    renderNotifications() {
        var container = document.getElementById('sync-messages-list');
        var markAllBtn = document.getElementById('sync-mark-all-read');

        if (!this._notifications || this._notifications.length === 0) {
            container.innerHTML = '<div class="vx-empty" id="sync-messages-empty"><div class="vx-empty-icon"><iconpark-icon name="message" size="48"></iconpark-icon></div><h3 class="vx-empty-title" data-tpl="sync_no_messages">暂无消息</h3></div>';
            if (typeof VXUI !== 'undefined' && VXUI.translateContainer) VXUI.translateContainer(container);
            if (markAllBtn) markAllBtn.style.display = 'none';
            return;
        }

        if (markAllBtn) {
            markAllBtn.style.display = this._unreadNotificationCount > 0 ? 'inline-block' : 'none';
        }

        var html = '';
        var self = this;
        this._notifications.forEach(function(n) {
            var classes = 'vx-sync-message-item' + (n.is_read ? '' : ' unread');
            html += '<div class="' + classes + '" onclick="VX_SYNC.openNotification(' + n.id + ')">' +
                '<div class="vx-sync-message-header">' +
                    '<span class="vx-sync-message-title">' + self.escapeHtml(n.title) + '</span>' +
                    '<span class="vx-sync-message-time">' + n.created_at + '</span>' +
                '</div>' +
                (n.content ? '<div class="vx-sync-message-content">' + self.escapeHtml(n.content) + '</div>' : '') +
            '</div>';
        });
        container.innerHTML = html;
    },

    async openNotification(id) {
        var n = this._notifications.find(function(item) { return item.id === id; });
        if (!n || n.is_read) return;

        try {
            await this.wsRequest('notification_mark_read', {
                notification_id: id,
            });
            n.is_read = true;
            this._unreadNotificationCount = Math.max(0, this._unreadNotificationCount - 1);
            this.updateUnreadBadge();
            this.renderNotifications();
        } catch (e) {
            console.error('mark read failed', e);
        }
    },

    async markAllNotificationsRead() {
        try {
            await this.wsRequest('notification_mark_all_read', {});
            this._notifications.forEach(function(n) { n.is_read = true; });
            this._unreadNotificationCount = 0;
            this.updateUnreadBadge();
            this.renderNotifications();
        } catch (e) {
            console.error('mark all read failed', e);
        }
    },

    updateUnreadBadge() {
        var badge = document.getElementById('sync-unread-badge');
        if (badge) {
            if (this._unreadNotificationCount > 0) {
                badge.textContent = this._unreadNotificationCount > 99 ? '99+' : this._unreadNotificationCount;
                badge.style.display = 'inline-block';
            } else {
                badge.style.display = 'none';
            }
        }
    },

    async loadUnreadCount() {
        try {
            var resp = await this.wsRequest('unread_count_req', {});
            if (resp.status !== 1) return;
            this._unreadNotificationCount = (resp.data && resp.data.count) || 0;
            this.updateUnreadBadge();
        } catch (e) {
            console.error('load unread count failed', e);
        }
    },

    // ========== Permission Helper ==========

    _currentUserHasWritePermission() {
        if (this.isHost) return true;
        return this._currentDrivePermission === 'read_write';
    },
};
