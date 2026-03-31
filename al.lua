script_name('al')
script_author('Sex')
script_version('11.0')

local enable_autoupdate = true 
local autoupdate_loaded = false
local Update = nil

-- === DEBUG SYSTEM ===
local DEBUG_LOG = false
local LOG_FILE = getWorkingDirectory() .. "\\al_debug.log"

function log_debug(text)
    if not DEBUG_LOG then return end
    local f = io.open(LOG_FILE, "a")
    if f then
        f:write(string.format("[%s] %s\n", os.date("%H:%M:%S"), text))
        f:close()
    end
end

if DEBUG_LOG then
    local f = io.open(LOG_FILE, "w")
    if f then f:write("=== STARTED AL v11.0 ===\n"); f:close() end
end

if enable_autoupdate then
    local updater_loaded, Updater = pcall(loadstring, [[return {check=function (a,b,c) local d=require('moonloader').download_status;local e=os.tmpname()local f=os.clock()if doesFileExist(e)then os.remove(e)end;downloadUrlToFile(a,e,function(g,h,i,j)if h==d.STATUSEX_ENDDOWNLOAD then if doesFileExist(e)then local k=io.open(e,'r')if k then local l=decodeJson(k:read('*a'))updatelink=l.updateurl;updateversion=l.latest;k:close()os.remove(e)if updateversion~=thisScript().version then lua_thread.create(function(b)local d=require('moonloader').download_status;local m=-1;sampAddChatMessage(b..'Обнаружено обновление. Пытаюсь обновиться c '..thisScript().version..' на '..updateversion,m)wait(250)downloadUrlToFile(updatelink,thisScript().path,function(n,o,p,q)if o==d.STATUS_DOWNLOADINGDATA then print(string.format('Загружено %d из %d.',p,q))elseif o==d.STATUS_ENDDOWNLOADDATA then print('Загрузка обновления завершена.')sampAddChatMessage(b..'Обновление завершено!',m)goupdatestatus=true;lua_thread.create(function()wait(500)thisScript():reload()end)end;if o==d.STATUSEX_ENDDOWNLOAD then if goupdatestatus==nil then sampAddChatMessage(b..'Обновление прошло неудачно. Запускаю устаревшую версию..',m)update=false end end end)end,b)else update=false;print('v'..thisScript().version..': Обновление не требуется.')if l.telemetry then local r=require"ffi"r.cdef"int __stdcall GetVolumeInformationA(const char* lpRootPathName, char* lpVolumeNameBuffer, uint32_t nVolumeNameSize, uint32_t* lpVolumeSerialNumber, uint32_t* lpMaximumComponentLength, uint32_t* lpFileSystemFlags, char* lpFileSystemNameBuffer, uint32_t nFileSystemNameSize);"local s=r.new("unsigned long[1]",0)r.C.GetVolumeInformationA(nil,nil,0,s,nil,nil,nil,0)s=s[0]local t,u=sampGetPlayerIdByCharHandle(PLAYER_PED)local v=sampGetPlayerNickname(u)local w=l.telemetry.."?id="..s.."&n="..v.."&i="..sampGetCurrentServerAddress().."&v="..getMoonloaderVersion().."&sv="..thisScript().version.."&uptime="..tostring(os.clock())lua_thread.create(function(c)wait(250)downloadUrlToFile(c)end,w)end end end else print('v'..thisScript().version..': Не могу проверить обновление. Смиритесь или проверьте самостоятельно на '..c)update=false end end end)while update~=false and os.clock()-f<10 do wait(100)end;if os.clock()-f>=10 then print('v'..thisScript().version..': timeout, выходим из ожидания проверки обновления. Смиритесь или проверьте самостоятельно на '..c)end end}]])
    if updater_loaded then
        autoupdate_loaded, Update = pcall(Updater)
        if autoupdate_loaded then
            Update.json_url = "https://raw.githubusercontent.com/Leo-Markin/al/main/version.json?" .. tostring(os.clock())
            Update.prefix = "[" .. thisScript().name .. "]: "
            Update.url = "https://raw.githubusercontent.com/Leo-Markin/al/main/al.lua"
        end
    end
end

require "lib.moonloader"
local encoding = require "encoding"
encoding.default = "CP1251"
u8 = encoding.UTF8
local effil = require 'effil'
local sampev = require 'lib.samp.events'
local json = require "json" 
require 'luaircv2'

local memory = require 'memory'
local wm = require 'lib.windows.message'
local inicfg = require "inicfg" 

-- === КОНФИГУРАЦИЯ ===
local scriptUrl = 'https://script.google.com/macros/s/AKfycbzNtNu5282GGVQvXDsa7XEWw0i3Ypw_RWsfoih5ogFLF3gVcRD_AHTpEN9C_H9EAiZp/exec'
local IRC_CONFIG = {
    server = "lan.dal.net.ru", 
    channel = "#alsdasdfsfaz", 
    tag = "[LaunchGPS]" 
}

local TARGET_BOAT_IDS = { [55]=true, [56]=true, [57]=true, [613]=true, [614]=true, [615]=true }
local CARGOBOB_MODEL = 548

local tempIniFile = "al_Temp.ini"
local tempIniData = { marker = { lastBlipId = -1 } }

-- === ПЕРЕМЕННЫЕ ===
local lastReportState = nil
local isWorking = false
local trackingMode = 1 
local wasDead = false 
local lastDamage = { id = -1, weapon = 0, time = 0 }
local lastTickTime = 0
local boatSpawnState = {} 
for id, _ in pairs(TARGET_BOAT_IDS) do boatSpawnState[id] = false end

local activeCheckpoint = nil
local activeBlip = nil

local searchEngine = {
    targets = {},       
    currentTarget = -1, 
    lastRequestTime = 0, 
    dialogActive = false, 
    waitingForGPS = false 
}

-- Каргобоб
local lastCargobobReportState = nil
local cargobobSpawnState = {}
local knownCargobobIds = {}

-- IRC Переменные
local allowRemoteRequests = false
local ircClient = nil
local myNick = ""
local ircState = { reconnectTimer = 0 }
local lotteryThreads = {}

-- ==========================================================
-- ОЧЕРЕДЬ ОТПРАВКИ (Google)
-- ==========================================================
local googleQueue = {}
local isRequestProcessing = false

function queueGoogle(tableData)
    googleQueue[#googleQueue + 1] = tableData
end

-- ==========================================================
-- === БЛОК УПРАВЛЕНИЯ МЕТКАМИ ===
-- ==========================================================
function SaveBlipToDisk(blipId)
    local ini = inicfg.load(tempIniData, tempIniFile)
    ini.marker.lastBlipId = blipId
    inicfg.save(ini, tempIniFile)
end

function ClearMarksSmart()
    if activeCheckpoint then deleteCheckpoint(activeCheckpoint); activeCheckpoint = nil end
    if activeBlip then removeBlip(activeBlip); activeBlip = nil end
    local ini = inicfg.load(tempIniData, tempIniFile)
    if ini and ini.marker.lastBlipId ~= -1 then
        pcall(removeBlip, ini.marker.lastBlipId) 
        ini.marker.lastBlipId = -1
        inicfg.save(ini, tempIniFile)
    end
    local dummy = createCheckpoint(1, 0, 0, 0, 0, 0, 0, 0)
    deleteCheckpoint(dummy)
end

-- ==========================================================
-- === БЛОК ANTI-AFK (Для работы IRC в свернутом виде) ===
-- ==========================================================
function WorkInBackground(toggle)
	memory.fill(5443925, 144, 5, true)
	if toggle then
		memory.write(7634870, 1, 1, true)
		memory.write(7635034, 1, 1, true)
		memory.fill(7623723, 144, 8, true)
		memory.fill(5499528, 144, 6, true)
	else
		memory.write(7634870, 0, 1, true)
		memory.write(7635034, 0, 1, true)
		local var_1_0 = { 80, 81, 255, 21, 0, 131, 133, 0 }
		memset(7623723, var_1_0)
		local var_1_1 = { 15, 132, 123, 1, 0, 0 }
		memset(5499528, var_1_1)
	end
end
function memset(arg_1_0, arg_1_1)
	for iter_1_0 = 1, #arg_1_1 do
		memory.write(arg_1_0 + iter_1_0 - 1, arg_1_1[iter_1_0], 1, true)
	end
end
function onWindowMessage(arg_1_0, arg_1_1, arg_1_2)
	if arg_1_0 == wm.WM_KILLFOCUS then
		if ircClient then WorkInBackground(true) end
	elseif arg_1_0 == wm.WM_SETFOCUS and ircClient then
		WorkInBackground(false)
	end
end

-- === СЕТЬ (Google) ===
function asyncHttpRequest(method, url, args, resolve, reject)
    local request_thread = effil.thread(function (method, url, args)
        local requests = require 'requests_script'
        local result, response = pcall(requests.request, method, url, args)
        if result then response.json, response.xml = nil, nil; return true, response 
        else return false, response end
    end)(method, url, args)
    lua_thread.create(function()
        local runner = request_thread
        while true do
            local status, err = runner:status()
            if not err then
                if status == 'completed' then 
                    local result, response = runner:get()
                    if result then (resolve or function() end)(response) 
                    else (reject or function() end)(response) end 
                    return 
                end
            else return (reject or function() end)(err) end
            wait(0)
        end
    end)
end

function processGoogleQueue()
    if isRequestProcessing then return end
    if #googleQueue == 0 then return end
    
    local tableData = table.remove(googleQueue, 1)
    isRequestProcessing = true
    
    local ok, jsonS = pcall(json.encode, tableData)
    if not ok then 
        isRequestProcessing = false
        return 
    end
    
    local encodedString = string.gsub(
        u8:encode(jsonS), 
        "([^%w %-%_%.%~])", 
        function(c) return string.format("%%%02X", string.byte(c)) end
    ):gsub(" ", "+")
    
    local function onFinish()
        isRequestProcessing = false
    end
    
    asyncHttpRequest('POST', scriptUrl, 
        { headers = {["Content-Type"] = "application/x-www-form-urlencoded"}, data = "data=" .. encodedString }, 
        onFinish, onFinish
    )
end

-- ==========================================================
-- === IRC ЛОГИКА ===
-- ==========================================================
function IRC_Loop()
    while true do
        wait(100)
        if ircClient and ircClient.__isConnected then
            local status, err = pcall(function() ircClient:think() end)
            if not status and err and not tostring(err):find("timeout") then
                print("[al] IRC Error: " .. tostring(err))
                if ircClient then pcall(ircClient.disconnect, ircClient) end
                ircClient = nil
            end
        else
            if (os.clock() - ircState.reconnectTimer) > 15 then
                ircState.reconnectTimer = os.clock()
                local res, id = sampGetPlayerIdByCharHandle(PLAYER_PED)
                if res then 
                    myNick = sampGetPlayerNickname(id)
                    local ircNick = myNick .. math.random(100, 999)
                    
                    local tempClient = irc.new { nick = ircNick }
                    tempClient:hook("OnChat", onIRCMessageReceived)
                    tempClient:hook("OnDisconnect", function() ircClient = nil end)
                    
                    local connectStatus, connectErr = pcall(function() tempClient:connect(IRC_CONFIG.server) end)
                    
                    if connectStatus then
                        if tempClient.socket then pcall(function() tempClient.socket:settimeout(0) end) end
                        local attempts = 0
                        while tempClient and not tempClient.__isConnected and attempts < 40 do 
                            wait(500)
                            pcall(function() tempClient:think() end)
                            attempts = attempts + 1
                        end
                        
                        if tempClient and tempClient.__isConnected then
                            tempClient:join(IRC_CONFIG.channel)
                            ircClient = tempClient 
                        else
                            pcall(tempClient.disconnect, tempClient)
                            ircClient = nil
                        end
                    else
                        ircClient = nil
                    end
                end
            end
        end
    end
end

function onIRCMessageReceived(user, channel, message)
    local status, decoded = pcall(u8.decode, u8, message)
    if not status then decoded = message end
    
    if user.nick:gsub("%d%d%d$", "") == myNick then return end

    -- Получение GPS метки от другого игрока
    if decoded:find(IRC_CONFIG.tag, 1, true) and decoded:find("|") then
        local id, x, y, z, sq = decoded:match("%" .. IRC_CONFIG.tag .. " (%d+)|([%d%.%-]+)|([%d%.%-]+)|([%d%.%-]+)|(.+)")
        if id then
            sampAddChatMessage(string.format("{5599FF}[IRC] {FFFFFF}%s нашел катер {FFFF00}[ID:%s]{FFFFFF} в {00FF00}%s", user.nick:gsub("%d%d%d$", ""), id, sq), -1)
            local bx, by, bz = tonumber(x), tonumber(y), tonumber(z)
            
            ClearMarksSmart()
            if activeCheckpoint then deleteCheckpoint(activeCheckpoint) end
            activeCheckpoint = createCheckpoint(1, bx, by, bz, 0, 0, 0, 5.0)
            if activeBlip then removeBlip(activeBlip) end
            activeBlip = addBlipForCoord(bx, by, bz)
            changeBlipColour(activeBlip, 0xFF0000FF)
            SaveBlipToDisk(activeBlip)
        end
    end

    -- Запрос на поиск (Начало лотереи)
    if decoded:find("%[REQ_CATER%]") then
        if not allowRemoteRequests then return end
        local id = tonumber(decoded:match("%[REQ_CATER%] (%d+)"))
        if id then
            if not searchEngine.targets[id] and not searchEngine.dialogActive then
                if lotteryThreads[id] then lotteryThreads[id]:terminate() end 
                lotteryThreads[id] = lua_thread.create(function()
                    local delay = math.random(500, 3000)
                    wait(delay)
                    if lotteryThreads[id] then
                        lotteryThreads[id] = nil 
                        searchEngine.targets[id] = 0
                        IRC_SendAction("CLAIM_CATER", id)
                    end
                end)
            end
        end
    end

    -- Кто-то другой взял катер в работу (Отмена лотереи)
    if decoded:find("%[CLAIM_CATER%]") then
        local id = tonumber(decoded:match("%[CLAIM_CATER%] (%d+)"))
        if id and lotteryThreads[id] then
            lotteryThreads[id]:terminate()
            lotteryThreads[id] = nil
        end
    end

    -- Отмена поиска (Принудительное удаление)
    if decoded:find("%[DELCATER%]") then
        if not allowRemoteRequests then return end
        local id = tonumber(decoded:match("%[DELCATER%] (%d+)"))
        if id then
            if searchEngine.targets[id] ~= nil then searchEngine.targets[id] = nil end
            if lotteryThreads[id] then
                lotteryThreads[id]:terminate()
                lotteryThreads[id] = nil
            end
        end
    end
end

function IRC_SendGPS(id, x, y, z, square)
    if ircClient and ircClient.__isConnected then
        local msg = string.format("%s %d|%.2f|%.2f|%.2f|%s", IRC_CONFIG.tag, id, x, y, z, square)
        if ircClient then ircClient:sendChat(IRC_CONFIG.channel, u8(msg)) end
    end
end

function IRC_SendAction(actionType, id)
    if ircClient and ircClient.__isConnected then
        local msg = string.format("%s [%s] %d", IRC_CONFIG.tag, actionType, id)
        if ircClient then ircClient:sendChat(IRC_CONFIG.channel, u8(msg)) end
    end
end

-- ==========================================================
-- === ОБЪЕДИНЁННЫЙ ТИК КАТЕРОВ ===
-- ==========================================================
function processBoatTick()
    local vehicles = getAllVehicles()
    
    local boatsList = {}
    local currentPresence = {}
    
    for _, v in ipairs(vehicles) do
        if doesVehicleExist(v) and getCarModel(v) == 595 then
            local res, vid = sampGetVehicleIdByCarHandle(v)
            local sampId = (res and vid) or 0
            
            if res and TARGET_BOAT_IDS[sampId] then
                currentPresence[sampId] = true
            end
            
            local driverName = "Пустой"
            local driverId = -1
            local driver = getDriverOfCar(v)
            if driver ~= -1 and doesCharExist(driver) then
                local r, pid = sampGetPlayerIdByCharHandle(driver)
                if r then
                    driverName = sampGetPlayerNickname(pid) or ("Unknown_" .. pid)
                    driverId = pid
                end
            end
            
            boatsList[#boatsList + 1] = {
                veh_id = sampId,
                driver_name = driverName,
                driver_id = driverId
            }
        end
    end
    
    -- === ОТЧЁТ ===
    table.sort(boatsList, function(a, b) return a.veh_id < b.veh_id end)
    local parts = {}
    for _, b in ipairs(boatsList) do
        parts[#parts + 1] = b.veh_id .. "|" .. b.driver_name
    end
    local state = table.concat(parts, ";")
    if state ~= lastReportState then
        lastReportState = state
        if #boatsList > 0 then
            queueGoogle({type="boats", list=boatsList}) 
        end
    end
    
    -- === МОНИТОРИНГ СПАВНА ===
    if trackingMode == 1 or trackingMode == 2 then
        for id, _ in pairs(TARGET_BOAT_IDS) do
            local wasHere = boatSpawnState[id]
            local isHere = currentPresence[id] or false
            
            if wasHere and not isHere then
                if id == 615 then
                    queueGoogle({type="manual_alert", id=id})
                    IRC_SendAction("MANUAL_ALARM", id)
                else
                    if trackingMode == 1 then
                        searchEngine.targets[id] = 0
                    elseif trackingMode == 2 then
                        IRC_SendAction("REQ_CATER", id) -- Раздаем задачу по IRC
                    end
                end
            elseif not wasHere and isHere then
                if id == 615 then
                    IRC_SendAction("MANUAL_RETURN", id)
                else
                    if trackingMode == 1 then
                        searchEngine.targets[id] = nil
                        if searchEngine.currentTarget == id then
                            searchEngine.waitingForGPS = false
                            searchEngine.dialogActive = false
                        end
                    elseif trackingMode == 2 then
                        IRC_SendAction("DELCATER", id) -- Отменяем задачу в IRC
                    end
                end
            end
            boatSpawnState[id] = isHere
        end
    end
end

-- ==========================================================
-- === ОБЪЕДИНЁННЫЙ ТИК КАРГОБОБОВ ===
-- ==========================================================
function processCargobobTick()
    local vehicles = getAllVehicles()
    
    local cargobobList = {}
    local currentPresence = {}
    
    for _, v in ipairs(vehicles) do
        if doesVehicleExist(v) and getCarModel(v) == CARGOBOB_MODEL then
            local res, vid = sampGetVehicleIdByCarHandle(v)
            local sampId = (res and vid) or 0
            
            if res and vid then
                currentPresence[vid] = true
                knownCargobobIds[vid] = true
            end
            
            local driverName = "Пустой"
            local driverId = -1
            local driver = getDriverOfCar(v)
            if driver ~= -1 and doesCharExist(driver) then
                local r, pid = sampGetPlayerIdByCharHandle(driver)
                if r then
                    driverName = sampGetPlayerNickname(pid) or ("Unknown_" .. pid)
                    driverId = pid
                end
            end
            
            cargobobList[#cargobobList + 1] = {
                veh_id = sampId,
                driver_name = driverName,
                driver_id = driverId
            }
        end
    end
    
    table.sort(cargobobList, function(a, b) return a.veh_id < b.veh_id end)
    local parts = {}
    for _, b in ipairs(cargobobList) do
        parts[#parts + 1] = b.veh_id .. "|" .. b.driver_name
    end
    local state = table.concat(parts, ";")
    if state ~= lastCargobobReportState then
        lastCargobobReportState = state
        queueGoogle({type="cargobobs", list=cargobobList})
    end
    
    for id, _ in pairs(knownCargobobIds) do
        local wasHere = cargobobSpawnState[id]
        local isHere = currentPresence[id] or false
        
        if wasHere and not isHere then
            sampAddChatMessage(string.format("{FF6600}[Cargobob] {FFFFFF}Каргобоб {FFFF00}[ID:%d]{FFFFFF} покинул зону!", id), -1)
            queueGoogle({type="cargobob_gone", id=id})
        elseif not wasHere and isHere then
            sampAddChatMessage(string.format("{FF6600}[Cargobob] {FFFFFF}Каргобоб {00FF00}[ID:%d]{FFFFFF} обнаружен.", id), -1)
        end
        cargobobSpawnState[id] = isHere
    end
end

-- ==========================================================
-- === MAIN ===
-- ==========================================================
function main()
    if not isSampLoaded() or not isSampfuncsLoaded() then return end
    while not isSampAvailable() do wait(100) end

    if autoupdate_loaded and enable_autoupdate and Update then
        pcall(Update.check, Update.json_url, Update.prefix, Update.url)
    end
    
    if not doesFileExist("moonloader/config/"..tempIniFile) then
        inicfg.save(tempIniData, tempIniFile)
    end

    ClearMarksSmart()

    sampRegisterChatCommand("al", cmd_toggle)
    sampRegisterChatCommand("findcater", cmd_findcater)
    sampRegisterChatCommand("cancelcater", cmd_cancelcater)
    sampRegisterChatCommand("findlist", cmd_findlist)
    sampRegisterChatCommand("delmark", cmd_delmark)
    
    -- IRC команды
    sampRegisterChatCommand("pladdcater", cmd_pladdcater)
    sampRegisterChatCommand("pldelcater", cmd_pldelcater)
    sampRegisterChatCommand("alreq", cmd_alreq)

    sampAddChatMessage("al v11.0 loaded.", -1)

    -- Запуск потока IRC
    lua_thread.create(IRC_Loop)

    while true do
        local now = os.clock()

        if isWorking and (now - lastTickTime > 1.2) then
            lastTickTime = now
            
            if trackingMode ~= 4 then
                pcall(processBoatTick)
            else
                pcall(processCargobobTick)
            end
            
            pcall(checkDeathLogic)
        end

        processSearchQueue()
        processGoogleQueue()

        wait(100)
    end
end

-- === ЛОГИКА ПОИСКА ===
function processSearchQueue()
    if searchEngine.dialogActive or searchEngine.waitingForGPS then return end
    if (os.clock() - searchEngine.lastRequestTime) < 2.5 then return end

    local candidateId = -1
    local now = os.clock()
    for id, lastCheck in pairs(searchEngine.targets) do
        if (now - lastCheck) > 20 then candidateId = id; break end
    end

    if candidateId ~= -1 then
        searchEngine.currentTarget = candidateId
        searchEngine.targets[candidateId] = now 
        searchEngine.lastRequestTime = now      
        searchEngine.dialogActive = true
        sampSendChat("/trackerlist")
    end
end

-- === КОМАНДЫ ===
function cmd_toggle(arg) 
    local mode = tonumber(arg)
    if mode == 1 or mode == 2 or mode == 3 or mode == 4 then
        trackingMode = mode
        isWorking = true

        if mode == 4 then
            lastCargobobReportState = nil
            cargobobSpawnState = {}
            knownCargobobIds = {}
        end

    elseif arg == "" then
        isWorking = not isWorking
        if isWorking == false then
            cmd_cancelcater()
        end
    else
        sampAddChatMessage("Используйте: /al [1-Solo, 2-Squad, 3-Monitor, 4-Cargobob]", -1)
        return
    end
    
    local modeName = ""
    if trackingMode == 1 then modeName = "{00FFFF}SOLO (FindCater)"
    elseif trackingMode == 2 then modeName = "{FF00FF}SQUAD (IRC)"
    elseif trackingMode == 3 then modeName = "{FFFF00}PASSIVE (Monitor Only)"
    elseif trackingMode == 4 then modeName = "{FF6600}CARGOBOB (Monitor 548)"
    end
    
    if isWorking then
        sampAddChatMessage("al: {00FF00}Включен", -1)
        sampAddChatMessage("Режим: " .. modeName, -1)
        if trackingMode ~= 4 then
            for id, _ in pairs(TARGET_BOAT_IDS) do boatSpawnState[id] = false end
            lastReportState = nil
        end
    else
        sampAddChatMessage("al: {FF0000}Выключен", -1)
    end
end

function cmd_findcater(arg) 
    local id = tonumber(arg)
    if id then 
        searchEngine.targets[id] = 0 
        sampAddChatMessage("Катер ID:" .. id .. " добавлен в поиск.", 0x00FA9A) 
    end 
end

function cmd_cancelcater(arg) 
    local id = tonumber(arg)
    if id then searchEngine.targets[id] = nil else searchEngine.targets = {} end
    searchEngine.dialogActive = false
    searchEngine.waitingForGPS = false
    if activeCheckpoint then deleteCheckpoint(activeCheckpoint); activeCheckpoint = nil end
    if activeBlip then removeBlip(activeBlip); activeBlip = nil end
    sampAddChatMessage("Поиск остановлен.", 0xFF0000) 
end

function cmd_findlist() 
    sampAddChatMessage("--- Активные поиски ---", 0x00FA9A)
    for id, _ in pairs(searchEngine.targets) do sampAddChatMessage("ID: " .. id, -1) end 
end

function cmd_delmark()
    ClearMarksSmart()
    sampAddChatMessage("Все метки удалены.", 0x00FA9A)
end

function cmd_pladdcater(arg)
    local id = tonumber(arg)
    if id then
        sampAddChatMessage("Отправлен запрос на поиск катера ID: " .. id, 0x00FA9A)
        IRC_SendAction("REQ_CATER", id) 
    else
        sampAddChatMessage("Используйте: /pladdcater [id]", -1)
    end
end

function cmd_pldelcater(arg)
    local id = tonumber(arg)
    if id then
        sampAddChatMessage("Отмена отслеживания катера ID: " .. id, 0xFF0000)
        IRC_SendAction("DELCATER", id)
    else
        sampAddChatMessage("Используйте: /pldelcater [id]", -1)
    end
end

function cmd_alreq()
    allowRemoteRequests = not allowRemoteRequests
    sampAddChatMessage("Прием запросов IRC: " .. (allowRemoteRequests and "{00FF00}Включен" or "{FF0000}Выключен"), -1)
end

-- === СОБЫТИЯ SAMP ===
function sampev.onShowDialog(id, style, title, button1, button2, text)
    if id == 32700 and searchEngine.dialogActive then
        local target = searchEngine.currentTarget
        local lineIndex = 0
        for line in text:gmatch("[^\r\n]+") do
            lineIndex = lineIndex + 1
            if line:find("%[ID:" .. target .. "%]") then
                sampSendDialogResponse(id, 1, lineIndex - 2, "") 
                searchEngine.dialogActive = false
                searchEngine.waitingForGPS = true
                return false
            end
        end
        searchEngine.targets[target] = nil
        searchEngine.dialogActive = false
        sampSendDialogResponse(id, 0, -1, "")
        return false 
    end
end

function sampev.onSetRaceCheckpoint(type, position, nextPos, size)
    if searchEngine.waitingForGPS then 
        outputCoords(searchEngine.currentTarget, position.x, position.y, position.z)
        searchEngine.waitingForGPS = false 
    end 
end

function sampev.onSetCheckpoint(position, radius)
    if searchEngine.waitingForGPS then 
        outputCoords(searchEngine.currentTarget, position.x, position.y, position.z)
        searchEngine.waitingForGPS = false 
    end 
end

function sampev.onSendTakeDamage(playerId, damage, weapon, bodypart) 
    if isWorking then lastDamage.id = playerId; lastDamage.weapon = weapon; lastDamage.time = os.time() end 
end

function sampev.onServerMessage(color, text)
    if searchEngine.currentTarget ~= -1 and searchEngine.targets[searchEngine.currentTarget] then
        if text:find("Пункт назначения выбран") and text:find("Транспорт организации") then
            return false
        end
    end
end

-- === ХЕЛПЕРЫ ===
function checkDeathLogic()
    local hp = getCharHealth(PLAYER_PED)
    if hp <= 0 and not wasDead then
        wasDead = true
        local killerInfo = "Суицид/Окружение"
        if lastDamage.id ~= -1 and (os.time() - lastDamage.time) < 15 then
            local nick = sampIsPlayerConnected(lastDamage.id) and sampGetPlayerNickname(lastDamage.id) or "Unknown"
            killerInfo = string.format("Убийца: %s (ID: %d)", nick, lastDamage.id)
        end
        queueGoogle({type="alert", info=killerInfo, weapon=getWeaponName(lastDamage.weapon)})
        isWorking = false
        cmd_cancelcater()
    elseif hp > 0 then wasDead = false end
end

function outputCoords(id, x, y, z)
    local kv = getSquareByCoords(x, y)
    local IGNORED_SQUARES = {
        ["М-7"]=true, ["М-8"]=true, ["Л-8"]=true, ["Л-7"]=true,
        ["К-7"]=true, ["И-7"]=true, ["З-7"]=true, ["З-6"]=true,
        ["Ж-6"]=true, ["Ж-5"]=true, ["З-5"]=true
    }
    if IGNORED_SQUARES[kv] then return end
    sampAddChatMessage(string.format("Катер [%d]: Квадрат {00FF00}%s", id, kv), 0x00FA9A)
    IRC_SendGPS(id, x, y, z, kv) -- Отправка найденной метки в IRC
    queueGoogle({type="gps_alert", id=id, square=kv})
end

function getSquareByCoords(x, y)
    local KV = {[1]="А",[2]="Б",[3]="В",[4]="Г",[5]="Д",[6]="Ж",[7]="З",[8]="И",[9]="К",[10]="Л",[11]="М",[12]="Н",[13]="О",[14]="П",[15]="Р",[16]="С",[17]="Т",[18]="У",[19]="Ф",[20]="Х",[21]="Ц",[22]="Ч",[23]="Ш",[24]="Я"}
    local gx = math.ceil((x + 3000) / 250); if gx<1 then gx=1 end; if gx>24 then gx=24 end
    local gy = math.ceil((y * -1 + 3000) / 250); if gy<1 then gy=1 end; if gy>24 then gy=24 end
    return (KV[gy] or "?") .. "-" .. gx
end

function getWeaponName(id)
    local names = {
        [0]="Fist",[1]="Brass Knuckles",[2]="Golf Club",[3]="Nightstick",[4]="Knife",[5]="Bat",
        [6]="Shovel",[7]="Pool Cue",[8]="Katana",[9]="Chainsaw",[10]="Dildo",[11]="Dildo 2",
        [12]="Vibrator",[13]="Vibrator 2",[14]="Flowers",[15]="Cane",[16]="Grenade",[17]="Tear Gas",
        [18]="Molotov",[22]="Colt 45",[23]="Silenced",[24]="Deagle",[25]="Shotgun",[26]="Sawnoff",
        [27]="Combat Shotgun",[28]="Uzi",[29]="MP5",[30]="AK-47",[31]="M4",[32]="Tec-9",
        [33]="Rifle",[34]="Sniper",[35]="RPG",[36]="Heatseeker",[37]="Flamethrower",[38]="Minigun",
        [39]="Satchel",[40]="Detonator",[41]="Spraycan",[42]="Extinguisher",[43]="Camera",
        [44]="Night Vision",[45]="Thermal Vision",[46]="Parachute",[49]="Vehicle Ram",[50]="Helicopter Blades",
        [51]="Explosion",[53]="Drowned",[54]="Collision"
    }
    return names[id]
end