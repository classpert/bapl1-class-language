

local lpeg = require "lpeg"
local pt = require "pt"

----------------------------------------------------
local function node (num)
  return {tag = "number", val = tonumber(num)}
end

local space = lpeg.S(" \t\n")^0
local numeral = lpeg.R("09")^1 / node  * space



local function parse (input)
  return numeral:match(input)
end

----------------------------------------------------

local function compile (ast)
  if ast.tag == "number" then
    return {"push", ast.val}
  end
end

----------------------------------------------------

local function run (code, stack)
  local pc = 1
  local top = 0
  while pc <= #code do
    if code[pc] == "push" then
      pc = pc + 1
      top = top + 1
      stack[top] = code[pc]
    else error("unknown instruction")
    end
    pc = pc + 1
  end
end


local input = io.read("a")
local ast = parse(input)
print(pt.pt(ast))
local code = compile(ast)
print(pt.pt(code))
local stack = {}
run(code, stack)
print(stack[1])
