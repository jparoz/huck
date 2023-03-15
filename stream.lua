-------------------------------
--                           --
--     it = co = stream()    --
--                           --
-------------------------------

-- A Stream is a function (closure)
--  which returns a coroutine,
--   which forms a Lua iterator
--    iterable with a Lua for loop.
-- The closure contains (as upvalues)
--  any state needed to form the coroutine,
--  such that a new coroutine is created
--   each time the Stream is evaluated.
-- This enables truly immutable semantics,
--  such that any Stream can be
--   evaluated multiple times,
--   evaluated once and then used again,
--   or any combination of these operations.


-- This flag decides whether
-- lists provided as an argument to fromList
-- are copied.
--
-- When false,
-- lists are not copied,
-- and if the originating list is mutated before the stream is consumed,
-- the stream will behave as though it was created using the modified list.
--
-- When true,
-- lists provided will be (shallow) copied,
-- such that the stream will always behave as though it was created
-- using the actual list elements provided at time of call to fromList.
local LIST_COPY <const> = false


local inspect = require "inspect"
local printi = function(...) return print(inspect(...)) end

local Stream = {}


--- Stream constructors
Stream.fromList = function(list)
    if LIST_COPY then
        local list_copy = {}
        for i, v in ipairs(list) do
            list_copy[i] = v
        end
        list = list_copy
    end

    return function()
        return coroutine.wrap(function()

            for _, x in ipairs(list) do
                coroutine.yield(x)
            end
        end)
    end
end

Stream.unfold = function(f, seed)
    return function()
        return coroutine.wrap(function()
            -- Capture the upvalue in a new local,
            -- to prevent modifying the original seed
            local seed = seed

            while true do
                local x
                x, seed = f(seed)
                if x == nil then break end
                coroutine.yield(x)
            end
        end)
    end
end

Stream.range = function(start, finish)
    return function()
        return coroutine.wrap(function()
            for i = start, finish do
                coroutine.yield(i)
            end
        end)
    end
end

Stream.rep = function(x)
    return function()
        return coroutine.wrap(function()
            while true do
                coroutine.yield(x)
            end
        end)
    end
end

Stream.cycle = function(stream)
    return function()
        return coroutine.wrap(function()
            while true do
                for x in stream() do
                    coroutine.yield(x)
                end
            end
        end)
    end
end


--- Stream transformers
Stream.map = function(f, stream)
    return function()
        return coroutine.wrap(function()
            for x in stream() do
                coroutine.yield(f(x))
            end
        end)
    end
end

Stream.filter = function(pred, stream)
    return function()
        return coroutine.wrap(function()
            for x in stream() do
                if pred(x) then coroutine.yield(x) end
            end
        end)
    end
end

Stream.flatten = function(stream)
    return function()
        return coroutine.wrap(function()
            for sub_stream in stream() do
                for x in sub_stream() do
                    coroutine.yield(x)
                end
            end
        end)
    end
end

Stream.flatmap = function(f, stream)
    return function()
        return coroutine.wrap(function()
            for x in stream() do
                local sub_stream = f(x)
                for y in sub_stream() do
                    coroutine.yield(y)
                end
            end
        end)
    end
end

Stream.take = function(n, stream)
    return function()
        return coroutine.wrap(function()
            local it = stream()
            for i = 1, n do
                coroutine.yield(it())
            end
        end)
    end
end

Stream.drop = function(n, stream)
    return function()
        return coroutine.wrap(function()
            local it = stream()

            -- Ignore the first n elements
            for i = 1, n do
                it()
            end

            -- Yield the rest of the items
            for x in it do
                coroutine.yield(x)
            end
        end)
    end
end


--- Stream evaluators
Stream.fold = function(f, acc, stream)
    for x in stream() do
        acc = f(x, acc)
    end
    return acc
end

Stream.collect = function(stream)
    local res = {}
    for item in stream() do
        res[#res+1] = item
    end
    return res
end


--- test start

-- local list = {1, 2, 3, 4, 5}
-- local iter = Stream.fromList(list)

local iter = Stream.range(1, 5)

iter = Stream.map(function(x) return x*3 end, iter)
iter = Stream.map(function(x) return x+1 end, iter)

-- iter = Stream.map(function(x) return 7/x end, iter)
-- iter = Stream.map(function(x) return tostring(x) end, iter)
-- iter = Stream.map(function(s) return #s end, iter)

iter = Stream.flatmap(function(x)
    return Stream.unfold(
        function(n)
            if n > 0 then
                return n, n-1
            end
        end,
        x
    )
end, iter)

iter = Stream.filter(function(n) return n % 2 == 0 end, iter)
iter = Stream.map(function(x) return x * 10 end, iter)

-- iter = Stream.map(function(x) return error("lol") end, iter)

printi(Stream.collect(iter))
print(Stream.fold(function(x, y) return x + y end, 0, iter))
-- table.insert(list, 123)
print(Stream.fold(function(x, y) return x + y end, 0, iter))

local unfolded = Stream.unfold(
    function(n)
        if n > 0 then
            return n, n-1
        end
    end,
    10
)

printi(Stream.collect(unfolded))
printi(Stream.collect(unfolded))

local threes = Stream.take(5, Stream.rep(3))
printi(Stream.collect(threes))
printi(Stream.collect(threes))

local taken = Stream.take(10, Stream.cycle(Stream.fromList({3, 10, 6})))
printi(Stream.collect(taken))
printi(Stream.collect(taken))

local dropped = Stream.drop(2, taken)
printi(Stream.collect(dropped))
printi(Stream.collect(dropped))

--- test end


return Stream
