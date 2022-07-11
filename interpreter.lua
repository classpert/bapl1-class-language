local lpeg = require "lpeg"
local pt = require "pt"

----------------------------------------------------
local function nodeNum (num)
  return {tag = "number", val = tonumber(num)}
end

local function nodeVar (var)
  return {tag = "variable", var = var}
end

local alpha = lpeg.R("AZ", "az")
local digit = lpeg.R("09")
local alphanum = alpha + digit

local space = lpeg.S(" \t\n")^0
local numeral = lpeg.R("09")^1 / nodeNum  * space

local ID = lpeg.C(alpha * alphanum^0) * space
local var = ID / nodeVar

local OP = "(" * space
local CP = ")" * space

local opA = lpeg.C(lpeg.S"+-") * space
local opM = lpeg.C(lpeg.S"*/") * space


-- Convert a list {n1, "+", n2, "+", n3, ...} into a tree
-- {...{ op = "+", e1 = {op = "+", e1 = n1, n2 = n2}, e2 = n3}...}
local function foldBin (lst)
  local tree = lst[1]
  for i = 2, #lst, 2 do
    tree = { tag = "binop", e1 = tree, op = lst[i], e2 = lst[i + 1] }
  end
  return tree
end

local factor = lpeg.V"factor"
local term = lpeg.V"term"
local exp = lpeg.V"exp"

grammar = lpeg.P{"exp",
  factor = numeral + OP * exp * CP + var,
  term = lpeg.Ct(factor * (opM * factor)^0) / foldBin,
  exp = lpeg.Ct(term * (opA * term)^0) / foldBin,
}

grammar = space * grammar * -1

local function parse (input)
  return grammar:match(input)
end

----------------------------------------------------

local function addCode (state, op)
  local code = state.code
  code[#code + 1] = op
end


local ops = {["+"] = "add", ["-"] = "sub",
             ["*"] = "mul", ["/"] = "div"}

local function codeExp (state, ast)
  if ast.tag == "number" then
    addCode(state, "push")
    addCode(state, ast.val)
  elseif ast.tag == "variable" then
    addCode(state, "load")
    addCode(state, ast.var)
  elseif ast.tag == "binop" then
    codeExp(state, ast.e1)
    codeExp(state, ast.e2)
    addCode(state, ops[ast.op])
  else error("invalid tree")
  end
end

local function compile (ast)
  local state = { code = {} }
  codeExp(state, ast)
  return state.code
end

----------------------------------------------------

local function run (code, mem, stack)
  local pc = 1
  local top = 0
  while pc <= #code do
    if code[pc] == "push" then
      pc = pc + 1
      top = top + 1
      stack[top] = code[pc]
    elseif code[pc] == "add" then
      stack[top - 1] = stack[top - 1] + stack[top]
      top = top - 1
    elseif code[pc] == "sub" then
      stack[top - 1] = stack[top - 1] - stack[top]
      top = top - 1
    elseif code[pc] == "mul" then
      stack[top - 1] = stack[top - 1] * stack[top]
      top = top - 1
    elseif code[pc] == "div" then
      stack[top - 1] = stack[top - 1] / stack[top]
      top = top - 1
    elseif code[pc] == "load" then
      pc = pc + 1
      local id = code[pc]
      top = top + 1
      stack[top] = mem[id]
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
local mem = {k0 = 0, k1 = 1, k10 = 10}
run(code, mem, stack)
print(stack[1])
