----------------------------------------------------------------
-- Radio Browser – Countries → Stations → Player (Ambernic)
-- 640x480 • Joystick-only • mpv external player • caching
----------------------------------------------------------------
local json = require("dkjson")

-- ---------- SETTINGS ----------
local W, H = 640, 480
local COUNTRIES_URL = "https://de1.api.radio-browser.info/json/countries?order=stationcount&reverse=true&limit=40"
local STATIONS_URL  = "https://de1.api.radio-browser.info/json/stations/search?countrycode=%s&order=clickcount&reverse=true&limit=10"

local SAVE_COUNTRIES = "countries_cache.json"
local SAVE_STATIONS_PREFIX = "stations_cache_" -- + <ISO>.json

local sel, scroll = 1, 0
local targetScroll = 0

local forceInstantScroll = false

-- ---------- STATE ----------
local state = "menu" -- "menu" | "countries" | "stations" | "player"
local joy, debounce, spinner = nil, 0, 0
local loading, loadingMsg = false, ""

-- lists
local countries, stations = {}, {}

-- selection + scroll
local rowH = 56
local listArea = { x=20, y=70, w=W-40, h=H-130 + 50 }

-- current context
local currentCountry, currentStation = nil, nil

-- mpv
local pid, player_process = nil, nil
local isPlaying, isBuffering, bufferTimer = false, false, 0

-- fonts
local fTitle, fItem, fSmall

----------------------------------------------------------------
-- MENU
----------------------------------------------------------------
local menuImages = {}
local menuIndex = 1
local menuFiles = {
  "assets/menu/Dashboard_AllRadios.png",
  "assets/menu/Dashboard_Fav.png",
  "assets/menu/Dashboard_Settings.png",
  "assets/menu/Dashboard_Exit.png"
}

-- === Equalizer Animado ===
local eqBars = {}
local eqNumBars = 6
local eqTime = 0

for i = 1, eqNumBars do
    eqBars[i] = {
        h = 20,
        speed = math.random(1,3) + math.random(),
        phase = math.random() * 3
    }
end


local carouselIndex = 1
local carouselPos   = 0
local carouselTarget = 0
local carouselSpeed  = 8

local countryCarouselPos = 1
local countryCarouselTarget = 1
local countryCarouselSpeed = 8


----------------------------------------------------------------
-- FS helpers
----------------------------------------------------------------
local function save_text(path, txt) return love.filesystem.write(path, txt) end
local function load_text(path)
  if not love.filesystem.getInfo(path) then return nil end
  return love.filesystem.read(path)
end
local function ensure_dirs()
  love.filesystem.createDirectory("flags")
  love.filesystem.createDirectory("flags/favicons")
end

function detectOS()
    local handle = io.popen("cat /etc/os-release 2>/dev/null")
    if not handle then
        return "unknown"
    end

    local result = handle:read("*a") or ""
    handle:close()

    -- Normaliza para minúsculas para facilitar
    local text = result:lower()

    if text:find("knulli") then
        return "knulli"
    elseif text:find("batocera") then
        return "batocera"
    elseif text:find("muos") then
        return "muos"
    elseif text:find("jelos") then
        return "jelos"
    end

    return "unknown"
end

local currentOS = detectOS()   -- usa a função que já te dei

-- Define o botão de OK conforme o OS
local btnOK = "a"   -- valor por defeito

if currentOS == "knulli" then
    btnOK = "b"
    btnSelect = "a"
elseif currentOS == "muos" then
    btnOK = "a"
    btnSelect = "b"
end


----------------------------------------------------------------
-- HTTP: LuaSocket first; curl fallback
----------------------------------------------------------------
local function fetch_url(url)
  local ok_http, http = pcall(require, "socket.http")
  if ok_http and http and http.request then
    if http.USERAGENT then http.USERAGENT = "Love2D/Ambernic" end
    local body, code = http.request(url)
    if code == 200 and body and #body > 0 then return true, body end
  end
  local cmd = string.format("curl -L --silent --fail '%s'", url)
  local p = io.popen(cmd)
  if not p then return false, nil end
  local body = p:read("*a")
  p:close()
  if body and #body > 0 then return true, body end
  return false, nil
end

----------------------------------------------------------------
-- Images: load safely (RGBA16 → RGBA8)
----------------------------------------------------------------
local function image_from_bytes(bytes, name)
  local okFD, fd = pcall(love.filesystem.newFileData, bytes, name or "img")
  if not okFD or not fd then return nil end
  local okID, imgData = pcall(love.image.newImageData, fd)
  if not okID or not imgData then return nil end
  local w, h = imgData:getDimensions()
  local converted = love.image.newImageData(w, h)
  converted:paste(imgData, 0, 0, 0, 0, w, h)
  return love.graphics.newImage(converted)
end

local function image_from_file(path)
  if not love.filesystem.getInfo(path) then return nil end
  local data = love.filesystem.read(path)
  if not data then return nil end
  return image_from_bytes(data, path)
end

----------------------------------------------------------------
-- Flags
----------------------------------------------------------------
local flagCache = {}
local function tryLoadFlag(countryName, codeISO)
  local key = (codeISO or "") .. "|" .. (countryName or "")
  if flagCache[key] ~= nil then return flagCache[key] end
  if codeISO and #codeISO > 0 then
    local p = string.format("flags/%s.png", codeISO)
    local img = image_from_file(p)
    if img then flagCache[key] = img; return img end
  end
  flagCache[key] = false
  return nil
end

local function drawFlagOrPlaceholder(name, code, x, y, w, h)
  local img = tryLoadFlag(name, code)
  if img then
    local iw, ih = img:getDimensions()
    local s = math.min(w/iw, h/ih)
    love.graphics.setColor(1,1,1); love.graphics.draw(img, x+(w-iw*s)/2, y+(h-ih*s)/2, 0, s, s)
  else
    love.graphics.setColor(0.2,0.2,0.25); love.graphics.rectangle("fill", x, y, w, h, 6,6)
    love.graphics.setColor(0.5,0.5,0.6); love.graphics.rectangle("line", x, y, w, h, 6,6)
    love.graphics.setColor(0.85,0.85,0.9)
    local codeText = (code and #code>0 and code) or (name and name:sub(1,2):upper()) or "??"
    love.graphics.print(codeText, x+6, y+h/2-6)
  end
end

----------------------------------------------------------------
-- Favicons
----------------------------------------------------------------
local faviconCache = {}
local function basename_from_url(url)
  if not url or #url==0 then return nil end
  local host = url:match("^https?://([^/]+)/") or url:match("^https?://([^/]+)$")
  local file = url:match(".*/([^/?#]+)") or ""
  if file == "" or not file:match("%.") then
    return (host or "favicon"):gsub(":%d+", "") .. ".png"
  end
  file = file:gsub("%.ico$", ".png")
  return file
end

local function load_or_download_favicon(url)
  if not url or #url==0 then return nil end
  if faviconCache[url] ~= nil then return faviconCache[url] end
  ensure_dirs()
  local fname = basename_from_url(url) or "favicon.png"
  local path = "flags/favicons/" .. fname
  local img = image_from_file(path)
  if img then faviconCache[url] = img; return img end
  local ok, body = fetch_url(url)
  if ok and body and #body > 0 then
    local tmpImg = image_from_bytes(body, fname)
    if tmpImg then
      save_text(path, body)
      faviconCache[url] = tmpImg
      return tmpImg
    end
  end
  faviconCache[url] = false
  return nil
end

local function drawFaviconOrPlaceholder(url, x, y, w, h)
  local img = load_or_download_favicon(url)
  if img then
    local iw, ih = img:getDimensions()
    local s = math.min(w/iw, h/ih)
    love.graphics.setColor(1,1,1); love.graphics.draw(img, x+(w-iw*s)/2, y+(h-ih*s)/2, 0, s, s)
  else
    love.graphics.setColor(0.25,0.27,0.33); love.graphics.rectangle("fill", x, y, w, h, 6,6)
    love.graphics.setColor(0.5,0.55,0.65); love.graphics.rectangle("line", x, y, w, h, 6,6)
  end
end



----------------------------------------------------------------
-- List helpers
----------------------------------------------------------------
local function ensureVisible()
  local top = math.floor(targetScroll / rowH) + 1
  local vis = math.floor(listArea.h / rowH)
  local bot = top + vis - 1

  if sel < top then
    targetScroll = (sel - 1) * rowH
  elseif sel > bot then
    targetScroll = (sel - vis) * rowH
  end
end

local function moveSelection(delta, size)
  sel = math.max(1, math.min(size, sel + delta))
  ensureVisible()
end

----------------------------------------------------------------
-- Data loading
----------------------------------------------------------------
local function load_countries()
  loading = true; loadingMsg = "A obter países…"
  local ok, body = fetch_url(COUNTRIES_URL)
  if ok and body then
    local data = json.decode(body)
    if data and type(data)=="table" then
      countries = {}
      for _, e in ipairs(data) do
        local name = e.name or e.country or e.title or "?"
        local code = e.countrycode or e.iso_3166_1 or e.code or ""
        table.insert(countries, { name = name, code = code })
      end
      table.sort(countries, function(a,b) return (a.name or ""):lower() < (b.name or ""):lower() end)
      save_text(SAVE_COUNTRIES, json.encode(countries))
      loading = false; return true
    end
  end
  local cache = load_text(SAVE_COUNTRIES)
  if cache then
    local data = json.decode(cache)
    if data then countries = data; loading = false; return true end
  end
  loading = false; return false
end

local function load_stations(code)
  if not code or #code==0 then return false end
  loading = true; loadingMsg = "A obter rádios…"
  local url = string.format(STATIONS_URL, code)
  local ok, body = fetch_url(url)
  if ok and body then
    local data = json.decode(body)
    if data and type(data)=="table" then
      stations = {}
      for _, s in ipairs(data) do
        table.insert(stations, {
          name      = s.name or s.station or s.title or "—",
          codec     = s.codec or "N/A",
          bitrate   = s.bitrate or 0,
          url       = s.url_resolved or s.url or "",
          favicon   = s.favicon or "",
          homepage  = s.homepage or "N/A",
          tags      = s.tags or "N/A",
          votes     = s.votes or 0,
          listeners = s.clickcount or 0,
        })
      end
      save_text(SAVE_STATIONS_PREFIX .. code .. ".json", json.encode(stations))
      loading = false; return true
    end
  end
  local cache = load_text(SAVE_STATIONS_PREFIX .. code .. ".json")
  if cache then
    local data = json.decode(cache)
    if data then stations = data; loading = false; return true end
  end
  loading = false; return false
end

----------------------------------------------------------------
-- Player (mpv)
----------------------------------------------------------------
local function stopPlayer()
  if pid then
    os.execute("kill " .. pid)
    if player_process then player_process:close() end
  end
  pid, player_process = nil, nil
  isPlaying, isBuffering, bufferTimer = false, false, 0
end

local function startPlayer(url)
  if not url or #url==0 then return end
  stopPlayer()
  isBuffering, bufferTimer = true, 0
  local cmd = string.format("mpv --no-video --really-quiet '%s' & echo $!", url)
  player_process = io.popen(cmd)
  if player_process then pid = player_process:read("*n") end
end

----------------------------------------------------------------
-- UI helpers
----------------------------------------------------------------
local function drawHeader(title, subtitle)
  love.graphics.setFont(fTitle)
  love.graphics.setColor(1,1,1)
  love.graphics.printf(title or "", 0, 16, W, "center")
  if subtitle and #subtitle>0 then
    love.graphics.setFont(fSmall)
    love.graphics.setColor(0.85,0.85,0.9)
    love.graphics.printf(subtitle, 0, 44, W, "center")
  end
end
local function drawListBackground()
  love.graphics.setColor(0.165, 0.616, 0.561)
  love.graphics.rectangle("fill", listArea.x-2, listArea.y-2, listArea.w+4, listArea.h+4, 10,10)
end
local function drawScrollBar(count)
  local contentH = count * rowH
  if contentH <= listArea.h then return end
  local barH = math.max(20, (listArea.h / contentH) * listArea.h)
  local barY = listArea.y + (scroll / (contentH - listArea.h)) * (listArea.h - barH)
  love.graphics.setColor(0.5,0.55,0.65,0.8)
  love.graphics.rectangle("fill", listArea.x + listArea.w - 8, barY, 6, barH, 3,3)
end
local function drawSpinner(cx, cy, r)
  for i=1,12 do
    local ang = spinner + (i/12)*2*math.pi
    local a = i/12
    love.graphics.setColor(1,1,1,a)
    love.graphics.circle("fill", cx + math.cos(ang)*r, cy + math.sin(ang)*r, 4)
  end
end

----------------------------------------------------------------
-- LOVE: LOAD
----------------------------------------------------------------
function love.load()
  love.window.setTitle("Radio Browser – Ambernic")
  love.window.setMode(W, H, {resizable=false})
  love.graphics.setBackgroundColor(0.12,0.14,0.18)

  ensure_dirs()

  fTitle = love.graphics.newFont(22)
  fItem  = love.graphics.newFont(16)
  fSmall = love.graphics.newFont(12)

  local joys = love.joystick.getJoysticks()
  if #joys > 0 then joy = joys[1] end

  -- Carregar imagens do menu
  for i, path in ipairs(menuFiles) do
    if love.filesystem.getInfo(path) then
      menuImages[i] = love.graphics.newImage(path)
    else
      print("⚠️ Missing menu image: " .. path)
    end
  end

  sel, scroll = 1, 0
end

----------------------------------------------------------------
-- LOVE: UPDATE
----------------------------------------------------------------
function love.update(dt)
  ----------------------------------------------------------------
  -- Spinner
  ----------------------------------------------------------------
  spinner = spinner + dt * 3
  if debounce > 0 then debounce = debounce - dt end

  ----------------------------------------------------------------
  -- Buffering / Player
  ----------------------------------------------------------------
  if isBuffering then
    bufferTimer = bufferTimer + dt
    if bufferTimer > 2.0 then
      isBuffering = false
      isPlaying   = true
    end
  end

  ----------------------------------------------------------------
  -- Equalizer sempre visível no player
  ----------------------------------------------------------------
  if state == "player" then
    if isPlaying or isBuffering then
      eqTime = eqTime + dt
      for i = 1, eqNumBars do
        eqBars[i].h = 15 + math.abs(math.sin(eqTime * eqBars[i].speed + eqBars[i].phase)) * 40
      end
    else
      for i = 1, eqNumBars do
        eqBars[i].h = 8
      end
    end
  end

  ----------------------------------------------------------------
  -- Animação do carrossel (usado em countries E stations)
  ----------------------------------------------------------------
  if (state == "countries" and #countries > 0) or (state == "stations" and #stations > 0) then
    local n = (state == "countries") and #countries or #stations
    local diff = carouselTarget - carouselPos

    if diff ~= 0 then
      -- caminho mais curto no carrossel circular
      if diff >  n/2 then diff = diff - n end
      if diff < -n/2 then diff = diff + n end

      local step = diff * math.min(1, dt * carouselSpeed)
      carouselPos = carouselPos + step

      if math.abs(diff) < 0.001 then
        carouselPos = carouselTarget
      end
    end
  end

  ----------------------------------------------------------------
  -- Se não há joystick, se está em debounce ou loading → sai
  ----------------------------------------------------------------
  if not joy or debounce > 0 or loading then return end

  ----------------------------------------------------------------
  -- MENU PRINCIPAL
  ----------------------------------------------------------------
  if state == "menu" then
    if joy:isGamepadDown("dpright") then
      menuIndex = menuIndex + 1
      if menuIndex > #menuImages then menuIndex = 1 end
      debounce = 0.2

    elseif joy:isGamepadDown("dpleft") then
      menuIndex = menuIndex - 1
      if menuIndex < 1 then menuIndex = #menuImages end
      debounce = 0.2

    elseif joy:isGamepadDown(btnOK) then
      debounce = 0.25
      if menuIndex == 1 then
        state = "countries"
        -- inicializar carrossel de países
        carouselPos    = 1.0
        carouselTarget = 1.0
        load_countries()

      elseif menuIndex == 4 then
        love.event.quit()

      else
        print("⚙️  Esta opção ainda não está disponível.")
      end
    end
    return
  end

  ----------------------------------------------------------------
  -- COUNTRIES – CARROSSEL HORIZONTAL
  ----------------------------------------------------------------
  if state == "countries" then

    local n = #countries
    if n > 0 then
      -- mover para o país seguinte (cards deslizam para a esquerda)
      if joy:isGamepadDown("dpright") then
        carouselTarget = carouselTarget + 1
        if carouselTarget > n then carouselTarget = 1 end
        debounce = 0.18

      -- mover para o país anterior (cards deslizam para a direita)
      elseif joy:isGamepadDown("dpleft") then
        carouselTarget = carouselTarget - 1
        if carouselTarget < 1 then carouselTarget = n end
        debounce = 0.18
      end

      -- ENTER / abrir rádios do país
      if joy:isGamepadDown(btnOK) then
        debounce = 0.2
        -- índice do país atualmente centrado
        local selIndex = math.floor(carouselPos + 0.5)
        if selIndex < 1 then selIndex = 1 end
        if selIndex > n then selIndex = n end

        currentCountry = countries[selIndex]

        -- ao entrar em stations, inicializar carrossel de rádios
        if load_stations(currentCountry.code) then
          state = "stations"
          carouselPos    = 1.0
          carouselTarget = 1.0
        else
          loadingMsg = "Sem ligação e sem cache."
        end
      end
    end

    -- VOLTAR ao menu
    if joy:isGamepadDown(btnSelect) then
      debounce = 0.2
      state = "menu"
    end

  ----------------------------------------------------------------
  -- STATIONS – CARROSSEL HORIZONTAL
  ----------------------------------------------------------------
  elseif state == "stations" then

    local n = #stations
    if n > 0 then
      -- mover para a estação seguinte (cards deslizam para a esquerda)
      if joy:isGamepadDown("dpright") then
        carouselTarget = carouselTarget + 1
        if carouselTarget > n then carouselTarget = 1 end
        debounce = 0.18

      -- mover para a estação anterior (cards deslizam para a direita)
      elseif joy:isGamepadDown("dpleft") then
        carouselTarget = carouselTarget - 1
        if carouselTarget < 1 then carouselTarget = n end
        debounce = 0.18
      end

      -- ENTER / PLAY
      if joy:isGamepadDown(btnOK) then
        debounce = 0.2
        local selIndex = math.floor(carouselPos + 0.5)
        if selIndex < 1 then selIndex = 1 end
        if selIndex > n then selIndex = n end
        currentStation = stations[selIndex]
        startPlayer(currentStation.url)
        state = "player"
      end
    end

    -- VOLTAR → países (mantém posição anterior do carrossel de países)
    if joy:isGamepadDown(btnSelect) then
      debounce = 0.2
      state = "countries"
    end

  ----------------------------------------------------------------
  -- PLAYER
  ----------------------------------------------------------------
  elseif state == "player" then

    if joy:isGamepadDown(btnOK) then
      debounce = 0.2
      if isPlaying or isBuffering then 
        stopPlayer() 
      else 
        startPlayer(currentStation and currentStation.url or "") 
      end
    end

    if joy:isGamepadDown(btnSelect) then
      debounce = 0.2
      stopPlayer()
      state = "stations"
    end

    -- 🌙 Controlo de brilho via L/R shoulder (só Knulli)
    if joy:isGamepadDown("leftshoulder") then
      debounce = 0.2
      brightness = math.max(0, (brightness or 100) - 10)
      os.execute("knulli-brightness " .. brightness)
      print(string.format("🌑 Brilho: %d%%", brightness))

    elseif joy:isGamepadDown("rightshoulder") then
      debounce = 0.2
      brightness = math.min(100, (brightness or 100) + 10)
      os.execute("knulli-brightness " .. brightness)
      print(string.format("🌕 Brilho: %d%%", brightness))
    end
  end
end


----------------------------------------------------------------
-- LOVE: DRAW
----------------------------------------------------------------
function love.draw()
  -------------------------------------------------------
  -- MENU
  -------------------------------------------------------
  if state == "menu" then
    love.graphics.setBackgroundColor(0.149, 0.275, 0.325)

    if menuImages[menuIndex] then
      local img = menuImages[menuIndex]
      local iw, ih = img:getDimensions()
      local s = math.min(W/iw, H/ih)
      love.graphics.setColor(1,1,1)
      love.graphics.draw(img, (W - iw*s)/2, (H - ih*s)/2, 0, s, s)
    else
      love.graphics.setColor(1,1,1)
      love.graphics.printf("Menu image not found", 0, H/2-10, W, "center")
    end

    love.graphics.setFont(fSmall)
    love.graphics.setColor(0.8,0.8,0.9)
    love.graphics.printf("← / → navegar  •  A selecionar", 0, H - 28, W, "center")
    return
  end

  -------------------------------------------------------
  -- LOADING
  -------------------------------------------------------
  if loading then
    drawHeader("Carregar…", "")
    drawSpinner(W/2, H/2 - 10, 28)
    love.graphics.setFont(fItem)
    love.graphics.setColor(1,1,1)
    love.graphics.printf(loadingMsg or "A carregar…", 0, H/2 + 26, W, "center")
    return
  end

  -------------------------------------------------------
  -- COUNTRIES – CARROSSEL HORIZONTAL
  -------------------------------------------------------
  -------------------------------------------------------
-- COUNTRIES – CARROSSEL HORIZONTAL (FIXED)
-------------------------------------------------------
  if state == "countries" then

      drawHeader("Choose a Country", "Top 40 by station count • A–Z")

      local centerX = W/2
      local centerY = H/2 + 10
      local cardW, cardH = 210, 160
      local spacing = 230
      local n = #countries

      if n == 0 then
          love.graphics.setFont(fItem)
          love.graphics.setColor(1,1,1)
          love.graphics.printf("Sem países disponíveis.", 0, H/2, W, "center")
          return
      end

      for i = 1, n do
          -- índice circular garantido (nunca desaparece)
          local idx = i

          -- cálculo relativo CORRIGIDO
          local rel = ((i - carouselPos + n/2) % n) - n/2

          -- ignorar apenas os que estão muito longe
          if math.abs(rel) <= 2.5 then

              -- SCALE SUAVE (zoom)
              local dist  = math.min(1, math.abs(rel))
              local scale = 1 - dist * 0.35

              local x = centerX + rel * spacing
              local y = centerY

              -- cartão central destacado
              if math.abs(rel) < 0.3 then
                  love.graphics.setColor(0.20, 0.16, 0.25, 0.90)
              else
                  love.graphics.setColor(0.12, 0.12, 0.15, 0.85)
              end

              love.graphics.rectangle(
                  "fill",
                  x - (cardW*scale)/2,
                  y - (cardH*scale)/2,
                  cardW*scale,
                  cardH*scale,
                  14, 14
              )

              local c = countries[idx]

              -- bandeira
              drawFlagOrPlaceholder(
                  c.name,
                  c.code,
                  x - 48*scale,
                  y - 60*scale,
                  96*scale,
                  64*scale
              )

              -- nome
              love.graphics.setColor(1,1,1)
              love.graphics.setFont(fItem)
              love.graphics.printf(
                  c.name or "N/A",
                  x - 90*scale,
                  y + 10*scale,
                  180*scale,
                  "center"
              )

              -- código ISO
              love.graphics.setFont(fSmall)
              love.graphics.setColor(0.85,0.85,0.9)
              love.graphics.printf(
                  c.code or "",
                  x - 90*scale,
                  y + 40*scale,
                  180*scale,
                  "center"
              )
          end
      end

      love.graphics.setFont(fSmall)
      love.graphics.setColor(0.85,0.85,0.9)
      love.graphics.printf("← / → navegar  •  A abrir rádios  •  B voltar", 0, H-26, W, "center")
      return
  end


  -------------------------------------------------------
  -- STATIONS – CARROSSEL HORIZONTAL COM ZOOM SUAVE
  -------------------------------------------------------
  -------------------------------------------------------
-- STATIONS – CARROSSEL HORIZONTAL COM LOOP INFINITO
-------------------------------------------------------
    if state == "stations" then

      drawHeader(
        string.format("Stations – %s (%s)", currentCountry.name or "?", currentCountry.code or "" ),
        "Top 10 por popularidade"
      )

      local centerX = W/2
      local centerY = H/2 + 10
      local cardW, cardH = 210, 210
      local spacing = 230
      local n = #stations

      if n == 0 then
        love.graphics.setFont(fItem)
        love.graphics.setColor(1,1,1)
        love.graphics.printf("Sem rádios disponíveis.", 0, H/2, W, "center")
        return
      end

      -- DESENHO DO CARROSSEL (COM WRAP CORRIGIDO)
      for i = 1, n do

          local s = stations[i]

          -- scroll infinito
          local rel = ((i - carouselPos + n/2) % n) - n/2

          if math.abs(rel) <= 2.5 then

              -- SCALE SUAVE
              local dist  = math.min(1, math.abs(rel))
              local scale = 1 - dist * 0.35

              local x = centerX + rel * spacing
              local y = centerY

              -- Destaque do cartão central
              if math.abs(rel) < 0.3 then
                  love.graphics.setColor(0.20,0.16,0.25,0.90)
              else
                  love.graphics.setColor(0.12,0.12,0.15,0.85)
              end

              love.graphics.rectangle(
                  "fill",
                  x - (cardW*scale)/2,
                  y - (cardH*scale)/2,
                  cardW*scale,
                  cardH*scale,
                  14, 14
              )

              -- favicon
              drawFaviconOrPlaceholder(
                s.favicon,
                x - 32*scale,
                y - 70*scale,
                64*scale,
                64*scale
              )

              ------------------------------------------------------
              -- 💡 MOSTRAR NOME E QUALIDADE APENAS NO ITEM CENTRAL
              ------------------------------------------------------
              if math.abs(rel) < 0.3 then
                  -- nome da rádio
                  love.graphics.setColor(1,1,1)
                  love.graphics.setFont(fItem)
                  love.graphics.printf(
                      s.name,
                      x - 90*scale,
                      y + 5*scale,
                      180*scale,
                      "center"
                  )

                  -- bitrate + codec
                  love.graphics.setFont(fSmall)
                  love.graphics.setColor(0.85,0.85,0.9)
                  love.graphics.printf(
                      string.format("%s • %dkbps", s.codec, s.bitrate),
                      x - 90*scale,
                      y + 40*scale,
                      180*scale,
                      "center"
                  )
              end
          end
      end

      love.graphics.setFont(fSmall)
      love.graphics.setColor(0.85,0.85,0.9)
      love.graphics.printf("← / → navegar  •  A tocar  •  B voltar", 0, H-26, W, "center")
      return
  end


  -------------------------------------------------------
  -- PLAYER
  -------------------------------------------------------
  if state == "player" then

    drawHeader(
      currentStation and (currentStation.name or "Playing") or "Playing",
      currentCountry and currentCountry.name or ""
    )

    local name   = currentStation.name or "N/A"
    local country= currentCountry.name or "N/A"
    local tags   = (currentStation.tags and #currentStation.tags>0) and currentStation.tags or "N/A"
    local bitrate= tonumber(currentStation.bitrate) or 0
    local codec  = currentStation.codec or "N/A"
    local qual   = (bitrate>0 and string.format("%d kbps %s", bitrate, codec)) or "N/A"
    local homepage = currentStation.homepage or "N/A"
    local votes  = currentStation.votes or 0
    local clicks = currentStation.listeners or 0

    love.graphics.setFont(fItem)
    love.graphics.setColor(1,1,1)

    local y = 82
    local function line(icon, text)
      love.graphics.printf(icon .. " " .. text, 40, y, W-80, "left")
      y = y + 26
    end

    line("🎵", name)
    line("📍", string.format("%s | %s", country, tags))
    line("📡", qual)
    line("🌐", homepage)
    line("❤️", string.format("%d Votes | 🔥 %d listeners", votes, clicks))

    y = y + 10
    love.graphics.setFont(fTitle)

    if isBuffering then
      love.graphics.setColor(1,1,1)
      love.graphics.printf("Buffering…", 0, y, W, "center")
    elseif isPlaying then
      love.graphics.setColor(0.3,0.9,0.3)
      love.graphics.printf("▶️  Play  (A = Pause)", 0, y, W, "center")
    else
      love.graphics.setColor(0.9,0.3,0.3)
      love.graphics.printf("⏸️  Pause  (A = Play)", 0, y, W, "center")
    end

    -- Equalizer
    local bx = W/2 - (eqNumBars * 14)/2
    local by = H - 90

    for i = 1, eqNumBars do
      local bar = eqBars[i]
      love.graphics.setColor(0.3, 0.9, 0.3)
      love.graphics.rectangle("fill", bx + (i-1)*14, by - bar.h, 10, bar.h, 3,3)
    end

    love.graphics.setFont(fSmall)
    love.graphics.setColor(0.85,0.85,0.9)
    love.graphics.printf("A Play/Pause  •  B voltar", 0, H-26, W, "center")
  end
end





----------------------------------------------------------------
-- CLEANUP
----------------------------------------------------------------
function love.quit()
  stopPlayer()
end
