local lpeg = require "lpeg"
local pt = require "pt"

----------------------------------------------------
local function node (num)
  return {tag = "number", val = tonumber(num)}
end


local function nodeUnOp (e)
  return {tag = "unop", op = "-", e = e}
end

local space = lpeg.S(" \t\n")^0

local OP = "(" * space
local CP = ")" * space

local opA = lpeg.C(lpeg.S"+-") * space
local opM = lpeg.C(lpeg.S"*/%") * space
local opE = lpeg.C("^") * space
local opUMin = "-" * space


local numeral
do
  local digit = lpeg.R("09")
  local hexa = digit + lpeg.R("af", "AF")
  numeral = (("0" * lpeg.S("xX") * hexa^1 + digit^1) / node) * space
end


-- Convert a list {n1, "+", n2, "+", n3, ...} into a tree
-- {...{ op = "+", e1 = {op = "+", e1 = n1, n2 = n2}, e2 = n3}...}
local function foldBin (lst)
  local tree = lst[1]
  for i = 2, #lst, 2 do
    tree = { tag = "binop", e1 = tree, op = lst[i], e2 = lst[i + 1] }
  end
  return tree
end

local primary = lpeg.V"primary"
local factor = lpeg.V"factor"
local prefixed = lpeg.V"prefixed"
local term = lpeg.V"term"
local exp = lpeg.V"exp"

grammar = lpeg.P{"exp",
  primary = numeral + OP * exp * CP,
  -- exponentiation is right associative
  factor = lpeg.Ct(primary * (opE * factor)^-1) / foldBin,
  prefixed = opUMin * factor / nodeUnOp + factor,
  term = lpeg.Ct(prefixed * (opM * prefixed)^0) / foldBin,
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
             ["*"] = "mul", ["/"] = "div", ["%"] = "mod", ["^"] = "exp",
            }

local unOps = {["-"] = "neg"}

local function codeExp (state, ast)
  if ast.tag == "number" then
    addCode(state, "push")
    addCode(state, ast.val)
  elseif ast.tag == "unop" then
    codeExp(state, ast.e)
    addCode(state, unOps[ast.op])
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

local function run (code, stack)
  local pc = 1
  local top = 0
  while pc <= #code do
    if code[pc] == "push" then
      pc = pc + 1
      top = top + 1
      stack[top] = code[pc]
    elseif code[pc] == "neg" then
      stack[top] = -stack[top]
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
    elseif code[pc] == "mod" then
      stack[top - 1] = stack[top - 1] % stack[top]
      top = top - 1
    elseif code[pc] == "exp" then
      stack[top - 1] = stack[top - 1] ^ stack[top]
      top = top - 1
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
