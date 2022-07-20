
local lpeg = require "lpeg"
local pt = require "pt"

----------------------------------------------------
local function I (msg)
  return lpeg.P(function () print(msg); return true end)
end


local function node (tag, ...)
  local labels = table.pack(...)
  local params = table.concat(labels, ", ")
  local fields = string.gsub(params, "(%w+)", "%1 = %1")
  local code = string.format(
    "return function (%s) return {tag = '%s', %s} end",
    params, tag, fields)
  return assert(load(code))()
end

----------------------------------------------------
local function nodeSeq (st1, st2)
  if st2 == nil then
    return st1
  else
    return {tag = "seq", st1 = st1, st2 = st2}
  end
end

local alpha = lpeg.R("AZ", "az")
local digit = lpeg.R("09")
local alphanum = alpha + digit

local comment = "#" * (lpeg.P(1) - "\n")^0


local maxmatch = 0
local space = lpeg.V"space"


local numeral = lpeg.R("09")^1 / tonumber /
                     node("number", "val")  * space

local reserved = {"return", "if", "else"}
local excluded = lpeg.P(false)
for i = 1, #reserved do
  excluded = excluded + reserved[i]
end
excluded = excluded * -alphanum

local ID = (lpeg.C(alpha * alphanum^0) - excluded) * space
local var = ID / node("variable", "var")


local function T (t)
  return t * space
end


local function Rw (t)
  assert(excluded:match(t))
  return t * -alphanum * space
end


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
local stat = lpeg.V"stat"
local stats = lpeg.V"stats"
local block = lpeg.V"block"

grammar = lpeg.P{"prog",
  prog = space * stats * -1,
  stats = stat * (T";" * stats)^-1 / nodeSeq,
  block = T"{" * stats * T";"^-1 * T"}",
  stat = block
       + Rw"if" * exp * block * (Rw"else" * block)^-1
           / node("if1", "cond", "th", "el")
       + ID * T"=" * exp / node("assgn", "id", "exp")
       + Rw"return" * exp / node("ret", "exp"),
  factor = numeral + T"(" * exp * T")" + var,
  term = lpeg.Ct(factor * (opM * factor)^0) / foldBin,
  exp = lpeg.Ct(term * (opA * term)^0) / foldBin,
  space = (lpeg.S(" \t\n") + comment)^0
            * lpeg.P(function (_,p)
                       maxmatch = math.max(maxmatch, p);
                       return true
                     end)
}


local function syntaxError (input, max)
  io.stderr:write("syntax error\n")
  io.stderr:write(string.sub(input, max - 10, max - 1),
        "|", string.sub(input, max, max + 11), "\n")
end

local function parse (input)
  local res = grammar:match(input)
  if (not res) then
    syntaxError(input, maxmatch)
    os.exit(1)
  end
  return res
end

----------------------------------------------------
local Compiler = { code = {}, vars = {}, nvars = 0 }

function Compiler:addCode (op)
  local code = self.code
  code[#code + 1] = op
end


local ops = {["+"] = "add", ["-"] = "sub",
             ["*"] = "mul", ["/"] = "div"}


function Compiler:var2num (id)
  local num = self.vars[id]
  if not num then
    num = self.nvars + 1
    self.nvars = num
    self.vars[id] = num
  end
  return num
end


function Compiler:currentPosition ()
  return #self.code
end


function Compiler:codeJmp (op)
  self:addCode(op)
  self:addCode(0)
  return self:currentPosition()
end


function Compiler:fixJmp2here (jmp)
  self.code[jmp] = self:currentPosition()
end


function Compiler:codeExp (ast)
  if ast.tag == "number" then
    self:addCode("push")
    self:addCode(ast.val)
  elseif ast.tag == "variable" then
    self:addCode("load")
    self:addCode(self:var2num(ast.var))
  elseif ast.tag == "binop" then
    self:codeExp(ast.e1)
    self:codeExp(ast.e2)
    self:addCode(ops[ast.op])
  else error("invalid tree")
  end
end


function Compiler:codeStat (ast)
  if ast.tag == "assgn" then
    self:codeExp(ast.exp)
    self:addCode("store")
    self:addCode(self:var2num(ast.id))
  elseif ast.tag == "seq" then
    self:codeStat(ast.st1)
    self:codeStat(ast.st2)
  elseif ast.tag == "ret" then
    self:codeExp(ast.exp)
    self:addCode("ret")
  elseif ast.tag == "if1" then
    self:codeExp(ast.cond)
    local jmp = self:codeJmp("jmpZ")
    self:codeStat(ast.th)
    if ast.el == nil then
      self:fixJmp2here(jmp)
    else
      local jmp2 = self:codeJmp("jmp")
      self:fixJmp2here(jmp)
      self:codeStat(ast.el)
      self:fixJmp2here(jmp2)
    end
  else error("invalid tree")
  end
end

local function compile (ast)
  Compiler:codeStat(ast)
  Compiler:addCode("push")
  Compiler:addCode(0)
  Compiler:addCode("ret")
  return Compiler.code
end

----------------------------------------------------

local function run (code, mem, stack)
  local pc = 1
  local top = 0
  while true do
  --[[
  io.write("--> ")
  for i = 1, top do io.write(stack[i], " ") end
  io.write("\n", code[pc], "\n")
  --]]
    if code[pc] == "ret" then
      return
    elseif code[pc] == "push" then
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
    elseif code[pc] == "store" then
      pc = pc + 1
      local id = code[pc]
      mem[id] = stack[top]
      top = top - 1
    elseif code[pc] == "jmp" then
      pc = code[pc + 1]
    elseif code[pc] == "jmpZ" then
      pc = pc + 1
      if stack[top] == 0 or stack[top] == nil then
        pc = code[pc]
      end
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
local mem = {}
run(code, mem, stack)
print(stack[1])
