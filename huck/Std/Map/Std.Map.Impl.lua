local M = {}

local clone = function(map)
    local new_map = {}
    for k, v in pairs(map) do
        new_map[k] = v
    end
    return new_map
end

M.lua_get = function(k)
    return function(map)
        return map[k]
    end
end

M.lua_insert = function(k)
    return function(v)
        return function(map)
            local new_map = clone(map)
            new_map[k] = v
            return new_map
        end
    end
end

M.lua_remove = function(k)
    return function(map)
        local new_map = clone(map)
        new_map[k] = nil
        return new_map
    end
end

M.lua_iter = function(map)
    -- @Note: relies upon a Huck value of type `[(a, b)]`
    -- being implemented as a Lua list of `{a, b}`s
    local stream = {}
    for k, v in pairs(map) do
        stream[#stream+1] = {k, v}
    end
    return stream
end

M.lua_collect = function(stream)
    -- @Note: relies upon a Huck value of type `[(a, b)]`
    -- being implemented as a Lua list of `{a, b}`s
    local map = {}
    for _, tuple in ipairs(stream) do
        map[tuple[1]] = tuple[2]
    end
    return map
end

return M
