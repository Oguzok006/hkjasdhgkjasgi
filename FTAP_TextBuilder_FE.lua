-- FTAP Text Builder (client executor script)
-- Uses FTAP's GrabEvents.SetNetworkOwner + PartOwner convention from the supplied source.
-- No Anchored changes, no character targeting, no restore-to-original-position teleport.
-- FE behavior depends on FTAP's server accepting the ownership request; not tested live.

local Players = game:GetService("Players")
local ReplicatedStorage = game:GetService("ReplicatedStorage")
local Workspace = game:GetService("Workspace")
local RunService = game:GetService("RunService")
local UserInputService = game:GetService("UserInputService")

local LocalPlayer = Players.LocalPlayer
local PlayerGui = LocalPlayer:WaitForChild("PlayerGui")
local GrabEvents = ReplicatedStorage:WaitForChild("GrabEvents", 10)
local SetNetworkOwner = GrabEvents and GrabEvents:FindFirstChild("SetNetworkOwner")

if not SetNetworkOwner or not SetNetworkOwner:IsA("RemoteEvent") then
    warn("FTAP Text Builder: GrabEvents.SetNetworkOwner was not found.")
    return
end

local FONT = {
    [" "] = {"000", "000", "000", "000", "000"},
    A = {"010", "101", "111", "101", "101"},
    B = {"110", "101", "110", "101", "110"},
    C = {"011", "100", "100", "100", "011"},
    D = {"110", "101", "101", "101", "110"},
    E = {"111", "100", "110", "100", "111"},
    F = {"111", "100", "110", "100", "100"},
    G = {"011", "100", "101", "101", "011"},
    H = {"101", "101", "111", "101", "101"},
    I = {"111", "010", "010", "010", "111"},
    J = {"001", "001", "001", "101", "010"},
    K = {"101", "101", "110", "101", "101"},
    L = {"100", "100", "100", "100", "111"},
    M = {"101", "111", "111", "101", "101"},
    N = {"101", "111", "111", "111", "101"},
    O = {"010", "101", "101", "101", "010"},
    P = {"110", "101", "110", "100", "100"},
    Q = {"010", "101", "101", "111", "011"},
    R = {"110", "101", "110", "101", "101"},
    S = {"011", "100", "010", "001", "110"},
    T = {"111", "010", "010", "010", "010"},
    U = {"101", "101", "101", "101", "111"},
    V = {"101", "101", "101", "101", "010"},
    W = {"101", "101", "111", "111", "101"},
    X = {"101", "101", "010", "101", "101"},
    Y = {"101", "101", "010", "010", "010"},
    Z = {"111", "001", "010", "100", "111"},
    ["0"] = {"111", "101", "101", "101", "111"},
    ["1"] = {"010", "110", "010", "010", "111"},
    ["2"] = {"110", "001", "010", "100", "111"},
    ["3"] = {"110", "001", "010", "001", "110"},
    ["4"] = {"101", "101", "111", "001", "001"},
    ["5"] = {"111", "100", "110", "001", "110"},
    ["6"] = {"011", "100", "110", "101", "010"},
    ["7"] = {"111", "001", "010", "010", "010"},
    ["8"] = {"010", "101", "010", "101", "010"},
    ["9"] = {"010", "101", "011", "001", "110"},
    ["!"] = {"010", "010", "010", "000", "010"},
    ["?"] = {"110", "001", "010", "000", "010"},
    ["."] = {"000", "000", "000", "000", "010"},
    [","] = {"000", "000", "000", "010", "100"},
    ["-"] = {"000", "000", "111", "000", "000"},
    ["'"] = {"010", "010", "000", "000", "000"},
    [":"] = {"000", "010", "000", "010", "000"},
    ["/"] = {"001", "001", "010", "100", "100"},
}

local CELL = 0.72
local MAX_TEXT_BYTES = 14
local OWNERSHIP_RANGE = 30
local OWNERSHIP_WAIT = 1.25
local MAX_FORCE = Vector3.new(1e9, 1e9, 1e9)
local ZERO = Vector3.new(0, 0, 0)

local currentBuild = nil
local currentHeartbeat = nil
local buildGeneration = 0
local guiDragConnection = nil

local function getCharacterParts()
    local character = LocalPlayer.Character
    if not character then return nil, nil end
    local head = character:FindFirstChild("Head")
    local root = character:FindFirstChild("HumanoidRootPart")
    if not head or not root then return nil, nil end
    return head, root
end

local function ownerName(part)
    local marker = part:FindFirstChild("PartOwner")
    if not marker and part.AssemblyRootPart then
        marker = part.AssemblyRootPart:FindFirstChild("PartOwner")
    end
    if marker and marker:IsA("StringValue") then
        return marker.Value
    end
    return nil
end

local function ownershipCFrame(origin, target)
    local direction = target - origin
    if direction.Magnitude < 1e-4 then
        return CFrame.new(origin)
    end
    direction = direction.Unit
    local worldUp = Vector3.new(0, 1, 0)
    local right = direction:Cross(worldUp)
    if right.Magnitude < 1e-4 then
        right = Vector3.new(1, 0, 0)
    else
        right = right.Unit
    end
    local up = right:Cross(direction).Unit
    return CFrame.fromMatrix(origin, right, up)
end

local function isExcluded(part, map)
    if not part:IsA("BasePart") then return true end
    if part.Anchored then return true end
    if map and part:IsDescendantOf(map) then return true end

    local cursor = part.Parent
    while cursor and cursor ~= Workspace do
        local lowerName = string.lower(cursor.Name)
        if lowerName == "grabparts" or lowerName == "debris" or lowerName == "effects" or lowerName == "effect" then
            return true
        end
        if cursor:IsA("Tool") or cursor:IsA("Accessory") then
            return true
        end
        if cursor:IsA("Model") and cursor:FindFirstChildOfClass("Humanoid") then
            return true -- excludes player characters and NPC humanoid models
        end
        cursor = cursor.Parent
    end

    for _, otherPlayer in ipairs(Players:GetPlayers()) do
        local character = otherPlayer.Character
        if character and part:IsDescendantOf(character) then
            return true
        end
    end
    return false
end

local function collectCandidates()
    local _, root = getCharacterParts()
    if not root then return {} end

    local map = Workspace:FindFirstChild("Map")
    local seenAssemblies = {}
    local candidates = {}

    for _, item in ipairs(Workspace:GetDescendants()) do
        if item:IsA("BasePart") and not isExcluded(item, map) then
            local assemblyRoot = item.AssemblyRootPart or item
            if assemblyRoot and not assemblyRoot.Anchored and not seenAssemblies[assemblyRoot] then
                local distance = (item.Position - root.Position).Magnitude
                if distance <= OWNERSHIP_RANGE then
                    seenAssemblies[assemblyRoot] = true
                    table.insert(candidates, item)
                end
            end
        end
    end
    return candidates
end

local function releaseBuild()
    buildGeneration = buildGeneration + 1
    if currentHeartbeat then
        currentHeartbeat:Disconnect()
        currentHeartbeat = nil
    end
    if currentBuild then
        for _, entry in ipairs(currentBuild.entries) do
            if entry.ownerWatch then
                entry.ownerWatch:Disconnect()
            end
            if entry.positionBody and entry.positionBody.Parent then
                entry.positionBody:Destroy()
            end
            if entry.gyroBody and entry.gyroBody.Parent then
                entry.gyroBody:Destroy()
            end
        end
    end
    currentBuild = nil
end

local function createPixels(text)
    local pixels = {}
    local normalized = string.upper(text)
    for charIndex = 1, #normalized do
        local char = normalized:sub(charIndex, charIndex)
        local glyph = FONT[char] or FONT["?"]
        for row = 1, 5 do
            for col = 1, 3 do
                if glyph[row]:sub(col, col) == "1" then
                    table.insert(pixels, {
                        x = (charIndex - 1) * 4 + col - 1,
                        y = row - 1,
                    })
                end
            end
        end
    end
    return pixels, math.max(1, #normalized * 4 - 1)
end

local function createMover(part)
    local bp = Instance.new("BodyPosition")
    bp.Name = "FTAPTextBuilder_Position"
    bp.P = 40000
    bp.D = 950
    bp.MaxForce = MAX_FORCE
    bp.Position = part.Position
    bp.Parent = part

    local bg = Instance.new("BodyGyro")
    bg.Name = "FTAPTextBuilder_Orientation"
    bg.P = 40000
    bg.D = 950
    bg.MaxTorque = MAX_FORCE
    bg.CFrame = part.CFrame
    bg.Parent = part

    return bp, bg
end

local function buildText(rawText, setStatus)
    releaseBuild()
    local myGeneration = buildGeneration
    local text = string.upper(tostring(rawText or "")):sub(1, MAX_TEXT_BYTES)
    if text:gsub("%s", "") == "" then
        setStatus("Введи текст.")
        return
    end

    local head, root = getCharacterParts()
    if not head or not root then
        setStatus("Персонаж не найден.")
        return
    end

    local pixels, width = createPixels(text)
    if #pixels == 0 then
        setStatus("В тексте нет собираемых символов.")
        return
    end

    local candidates = collectCandidates()
    if #candidates == 0 then
        setStatus("Нет подходящих незакреплённых объектов в радиусе 30 studs.")
        return
    end

    task.spawn(function()
        local _, currentRoot = getCharacterParts()
        if not currentRoot then
            setStatus("Персонаж не найден.")
            return
        end

        local requests = 0
        for i, part in ipairs(candidates) do
            if myGeneration ~= buildGeneration then return end
            if part.Parent and ownerName(part) ~= LocalPlayer.Name then
                local _, hrp = getCharacterParts()
                if hrp and (part.Position - hrp.Position).Magnitude <= OWNERSHIP_RANGE then
                    pcall(function()
                        SetNetworkOwner:FireServer(part, ownershipCFrame(hrp.Position, part.Position))
                    end)
                    requests = requests + 1
                end
            end
            if i % 8 == 0 then
                setStatus(string.format("Запрос владения: %d/%d", i, #candidates))
                task.wait(0.03)
            end
        end

        local deadline = os.clock() + OWNERSHIP_WAIT
        repeat
            if myGeneration ~= buildGeneration then return end
            local ownedCount = 0
            for _, part in ipairs(candidates) do
                if part.Parent and ownerName(part) == LocalPlayer.Name then
                    ownedCount = ownedCount + 1
                end
            end
            if ownedCount > 0 then break end
            task.wait(0.05)
        until os.clock() >= deadline

        if myGeneration ~= buildGeneration then return end
        local owned = {}
        for _, part in ipairs(candidates) do
            if part.Parent and not part.Anchored and ownerName(part) == LocalPlayer.Name then
                table.insert(owned, part)
            end
        end

        if #owned == 0 then
            setStatus("FTAP не выдал владение объектами. Ничего не перемещено.")
            return
        end

        local entries = {}
        for i, part in ipairs(owned) do
            local pixelIndex
            local layer
            if #owned <= #pixels then
                pixelIndex = math.floor((i - 1) * #pixels / #owned) + 1
                layer = 0
            else
                pixelIndex = ((i - 1) % #pixels) + 1
                layer = math.floor((i - 1) / #pixels)
            end

            local bp, bg = createMover(part)
            local entry = {
                part = part,
                positionBody = bp,
                gyroBody = bg,
                pixel = pixels[pixelIndex],
                layer = layer,
                ownerWatch = nil,
            }

            entry.ownerWatch = part.ChildAdded:Connect(function(child)
                if child.Name == "PartOwner" and child:IsA("StringValue") and child.Value ~= LocalPlayer.Name then
                    if bp.Parent then bp.MaxForce = ZERO end
                    if bg.Parent then bg.MaxTorque = ZERO end
                end
            end)

            table.insert(entries, entry)
        end

        if myGeneration ~= buildGeneration then
            for _, entry in ipairs(entries) do
                if entry.ownerWatch then entry.ownerWatch:Disconnect() end
                if entry.positionBody then entry.positionBody:Destroy() end
                if entry.gyroBody then entry.gyroBody:Destroy() end
            end
            return
        end

        currentBuild = {
            entries = entries,
            width = width,
        }

        currentHeartbeat = RunService.Heartbeat:Connect(function()
            local liveHead, liveRoot = getCharacterParts()
            if not liveHead or not liveRoot or not currentBuild then return end

            local right = liveRoot.CFrame.RightVector
            local forward = liveRoot.CFrame.LookVector
            local base = liveHead.Position + Vector3.new(0, 4.5, 0)
            local rotation = CFrame.lookAt(Vector3.zero, forward, Vector3.new(0, 1, 0))

            for _, entry in ipairs(currentBuild.entries) do
                local part = entry.part
                local bp = entry.positionBody
                local bg = entry.gyroBody
                if part.Parent and bp.Parent and bg.Parent then
                    if ownerName(part) == LocalPlayer.Name then
                        bp.MaxForce = MAX_FORCE
                        bg.MaxTorque = MAX_FORCE
                        local x = (entry.pixel.x - (currentBuild.width - 1) / 2) * CELL
                        local y = (2 - entry.pixel.y) * CELL
                        bp.Position = base + right * x + Vector3.new(0, y, 0) - forward * (entry.layer * CELL)
                        bg.CFrame = rotation
                    else
                        bp.MaxForce = ZERO
                        bg.MaxTorque = ZERO
                    end
                end
            end
        end)

        local missing = math.max(0, #pixels - #owned)
        if missing > 0 then
            setStatus(string.format("Собрано частично: %d объектов; не хватает %d пикселей.", #owned, missing))
        else
            setStatus(string.format("Готово: %d объектов. FE зависит от выданного FTAP владения.", #owned))
        end
    end)
end

-- GUI
local oldGui = PlayerGui:FindFirstChild("FTAPTextBuilderGUI")
if oldGui then oldGui:Destroy() end

local gui = Instance.new("ScreenGui")
gui.Name = "FTAPTextBuilderGUI"
gui.ResetOnSpawn = false
gui.DisplayOrder = 999
gui.Parent = PlayerGui

local frame = Instance.new("Frame")
frame.Name = "Main"
frame.Size = UDim2.fromOffset(360, 166)
frame.Position = UDim2.new(0.5, -180, 0.18, 0)
frame.BackgroundColor3 = Color3.fromRGB(27, 29, 35)
frame.BorderSizePixel = 0
frame.Active = true
frame.Parent = gui

local frameCorner = Instance.new("UICorner")
frameCorner.CornerRadius = UDim.new(0, 8)
frameCorner.Parent = frame

local titleBar = Instance.new("Frame")
titleBar.Name = "TitleBar"
titleBar.Size = UDim2.new(1, 0, 0, 32)
titleBar.BackgroundColor3 = Color3.fromRGB(39, 43, 53)
titleBar.BorderSizePixel = 0
titleBar.Active = true
titleBar.Parent = frame

local titleCorner = Instance.new("UICorner")
titleCorner.CornerRadius = UDim.new(0, 8)
titleCorner.Parent = titleBar

local title = Instance.new("TextLabel")
title.Size = UDim2.new(1, -16, 1, 0)
title.Position = UDim2.fromOffset(10, 0)
title.BackgroundTransparency = 1
title.Text = "FTAP | Text Builder"
title.TextXAlignment = Enum.TextXAlignment.Left
title.TextColor3 = Color3.fromRGB(240, 242, 250)
title.Font = Enum.Font.GothamBold
title.TextSize = 14
title.Parent = titleBar

local input = Instance.new("TextBox")
input.Name = "TextInput"
input.Size = UDim2.new(1, -20, 0, 34)
input.Position = UDim2.fromOffset(10, 42)
input.BackgroundColor3 = Color3.fromRGB(45, 48, 58)
input.BorderSizePixel = 0
input.TextColor3 = Color3.fromRGB(245, 245, 245)
input.PlaceholderColor3 = Color3.fromRGB(160, 164, 176)
input.PlaceholderText = "Hello, world! (Latin letters/numbers)"
input.Text = ""
input.ClearTextOnFocus = false
input.Font = Enum.Font.Gotham
input.TextSize = 14
input.Parent = frame
local inputCorner = Instance.new("UICorner")
inputCorner.CornerRadius = UDim.new(0, 5)
inputCorner.Parent = input

local function makeButton(name, label, x, width, color)
    local button = Instance.new("TextButton")
    button.Name = name
    button.Size = UDim2.fromOffset(width, 31)
    button.Position = UDim2.fromOffset(x, 84)
    button.BackgroundColor3 = color
    button.BorderSizePixel = 0
    button.Text = label
    button.TextColor3 = Color3.new(1, 1, 1)
    button.Font = Enum.Font.GothamBold
    button.TextSize = 12
    button.Parent = frame
    local corner = Instance.new("UICorner")
    corner.CornerRadius = UDim.new(0, 5)
    corner.Parent = button
    return button
end

local buildButton = makeButton("Build", "СОБРАТЬ", 10, 164, Color3.fromRGB(57, 99, 190))
local releaseButton = makeButton("Release", "ОТПУСТИТЬ", 184, 166, Color3.fromRGB(132, 65, 65))

local status = Instance.new("TextLabel")
status.Name = "Status"
status.Size = UDim2.new(1, -20, 0, 35)
status.Position = UDim2.fromOffset(10, 122)
status.BackgroundTransparency = 1
status.Text = "Ожидание. Объекты Map и персонажи исключены."
status.TextColor3 = Color3.fromRGB(195, 199, 210)
status.TextXAlignment = Enum.TextXAlignment.Left
status.TextYAlignment = Enum.TextYAlignment.Top
status.TextWrapped = true
status.Font = Enum.Font.Gotham
status.TextSize = 11
status.Parent = frame

local function setStatus(text)
    if status and status.Parent then
        status.Text = tostring(text)
    end
end

buildButton.MouseButton1Click:Connect(function()
    buildText(input.Text, setStatus)
end)

releaseButton.MouseButton1Click:Connect(function()
    local count = currentBuild and #currentBuild.entries or 0
    releaseBuild()
    setStatus(string.format("Освобождено %d объектов. Координаты не сбрасывались.", count))
end)

-- Drag the GUI by its title bar.
do
    local dragging = false
    local dragStart = nil
    local startPosition = nil

    titleBar.InputBegan:Connect(function(inputObject)
        if inputObject.UserInputType == Enum.UserInputType.MouseButton1
            or inputObject.UserInputType == Enum.UserInputType.Touch then
            dragging = true
            dragStart = inputObject.Position
            startPosition = frame.Position
            inputObject.Changed:Connect(function()
                if inputObject.UserInputState == Enum.UserInputState.End then
                    dragging = false
                end
            end)
        end
    end)

    guiDragConnection = UserInputService.InputChanged:Connect(function(inputObject)
        if dragging and (inputObject.UserInputType == Enum.UserInputType.MouseMovement
            or inputObject.UserInputType == Enum.UserInputType.Touch) then
            local delta = inputObject.Position - dragStart
            frame.Position = UDim2.new(
                startPosition.X.Scale,
                startPosition.X.Offset + delta.X,
                startPosition.Y.Scale,
                startPosition.Y.Offset + delta.Y
            )
        end
    end)
end

gui.Destroying:Connect(function()
    releaseBuild()
    if guiDragConnection then
        guiDragConnection:Disconnect()
        guiDragConnection = nil
    end
end)
