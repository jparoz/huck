local M = {}

-- @Fixme:
-- One could produce incorrectly typed values in Huck like so:
--
--      goodList = Std.List.collect [1, 2, 3];
--      goodMap = Std.Map.collect [(1, "one"), (2, "two"), (3, "three")];
--      badMap = getMap $ mkTable goodList goodMap;
--
-- Not sure what the solution is,
-- but this is not great.
M.lua_getList = function(t) return t end
M.lua_getMap  = function(t) return t end

-- @Note:
-- If the map has integer keys, they might be overwritten by the list elements.
M.lua_mkTable = function(list)
    return function(map)
        local t = {}
        for k, v in pairs(map) do
            t[k] = v
        end
        for i, v in ipairs(list) do
            t[i] = v
        end
        return t
    end
end

return M
