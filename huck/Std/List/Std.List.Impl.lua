local M = {}

local clone = function(list)
    local new_list = {}
    for i, v in ipairs(list) do
        new_list[i] = v
    end
    return new_list
end

M.lua_index = function(ix)
    return function(list)
        return list[ix]
    end
end

M.lua_insert = function(ix)
    return function(elem)
        return function(list)
            local new_list = clone(list)
            if ix < 0       then ix = 0       end
            if ix > #list+1 then ix = #list+1 end
            table.insert(new_list, ix, elem)
            return new_list
        end
    end
end

M.lua_remove = function(ix)
    return function(list)
        local new_list = clone(list)
        if ix < 0       then ix = 0       end
        if ix > #list+1 then ix = #list+1 end
        table.remove(new_list, ix)
        return new_list
    end
end

M.lua_replace = function(ix)
    return function(elem)
        return function(list)
            local new_list = clone(list)
            if ix < 0       then ix = 0       end
            if ix > #list+1 then ix = #list+1 end
            new_list[ix] = elem
            return new_list
        end
    end
end

M.lua_push = function(elem)
    return function(list)
        local new_list = clone(list)
        table.insert(new_list, elem)
        return new_list
    end
end

M.lua_pop = function(list)
    local new_list = clone(list)
    table.remove(new_list)
    return new_list
end

return M
