local Object = {}
Object.__index = Object

function Object.new()
    return setmetatable({x = 0}, Object)
end

function Object:activate()
    self.x = self.x + 1
    print("Incremented x.")
end

function Object:getVal()
    return self.x
end

return Object
