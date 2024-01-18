
local lpeg = require "lpeg"
local pt = require "pt"


local function I (msg)
  return lpeg.P(function (_, i) print(msg, i); return true end)
end


local function err (msg, ...)
  io.stderr:write(string.format(msg, ...), "\n")
  os.exit(false)
end
----------------------------------------------------
local function I (msg)
  return lpeg.P(function () print(msg); return true end)
end


local function node (tag, ...)
  local labels = {...}
  return function (...)
    local params = {...}
    local t = {tag = tag}
    for i = 1, #labels do
      t[labels[i]] = params[i]
    end
    return t
  end
end

----------------------------------------------------
local function nodeSeq (st1, st2)
  if st2 == nil then
    return st1
  else
    return {tag = "seq", st1 = st1, st2 = st2}
  end
end

local alpha = lpeg.R("AZ", "az", "__")
local digit = lpeg.R("09")
local alphanum = alpha + digit

local comment
do
  local missEnd = lpeg.P(function ()
    err("unfinished long comment")
  end)
  comment = "#{" * (lpeg.P(1) - "#}")^0 * (lpeg.P"#}" + missEnd)
          + "#" * (lpeg.P(1) - "\n")^0
end


local maxmatch = 0
local space = lpeg.V"space"


local reserved = {"return", "if", "elseif", "else", "while", "and", "or"}
for i = 1, #reserved do   -- invert table
  reserved[reserved[i]] = true
  reserved[i] = nil
end


local ID = (lpeg.C(alpha * alphanum^0))
ID = lpeg.Cmt(ID, function (_, _, id)   -- filter valid identifiers
                    if not reserved[id] then
                      return true, id
                    else  -- 'id' is a reserved word
                      return false  -- match will fail
                    end
                  end) * space
local var = ID / node("variable", "var")


local function T (t)
  return t * space
end


local function Rw (t)
  assert(reserved[t])
  return t * -alphanum * space
end


local opA = lpeg.C(lpeg.S"+-") * space
local opM = lpeg.C(lpeg.S"*/%") * space
local opE = lpeg.C("^") * space
local unOp = lpeg.C(lpeg.S"-!") * space
local opComp = lpeg.C(lpeg.P(">=") + "<=" + "==" + "!=" + "<" + ">") * space


local numeral
do
  local hexadigit = digit + lpeg.R("af", "AF")
  local hexanum = "0" * lpeg.S("xX") * hexadigit^1
  local exponent = lpeg.S("eE") * lpeg.S("+-")^-1 * digit^1
  local decimal = digit^1 * lpeg.P("." * digit^0)^-1 + "." * digit^1
  decimal = decimal * exponent^-1
  numeral = ((hexanum + decimal) / tonumber / node("number", "val"))
  numeral = numeral * space
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


local function foldLog (op)
  return function (lst)
    local tree = lst[1]
    for i = 2, #lst do
      tree = { tag = "logop", e1 = tree, op = op, e2 = lst[i] }
    end
    return tree
  end
end

-- To be reused by 'if' and 'elseif'
local nodeIf = node("if1", "cond", "th", "el")

local primary = lpeg.V"primary"
local factor = lpeg.V"factor"
local prefixed = lpeg.V"prefixed"
local term = lpeg.V"term"   -- multiplicative expressions
local addexp = lpeg.V"addexp"   -- additive expressions
local compexp = lpeg.V"compexp"   -- comparative expressions
local andexp = lpeg.V"andexp"   -- 'and' expressions
local exp = lpeg.V"exp"   -- 'or' expressions
local stat = lpeg.V"stat"
local restif = lpeg.V"restif"
local stats = lpeg.V"stats"
local block = lpeg.V"block"

grammar = lpeg.P{"prog",
  prog = space * stats * -1,
  stats = stat * (T";" * stats)^-1 / nodeSeq,
  block = T"{" * stats * T";"^-1 * T"}",
  stat = block
       + T"@" * exp / node("print", "exp")
       + Rw"if" * exp * block * restif / nodeIf
       + Rw"while" * exp * block / node("while1", "cond", "body")
       + ID * T"=" * exp / node("assgn", "id", "exp")
       + Rw"return" * exp / node("ret", "exp")
       + lpeg.Cc{tag = "nop"},   -- empty statement
  restif = (Rw"elseif" * exp * block * restif / nodeIf
         +  Rw"else" * block)^-1,
  primary = numeral + T"(" * exp * T")" + var,
  -- exponentiation is right associative
  factor = lpeg.Ct(primary * (opE * factor)^-1) / foldBin,
  prefixed = unOp * prefixed / node("unop", "op", "e") + factor,
  term = lpeg.Ct(prefixed * (opM * prefixed)^0) / foldBin,
  addexp = lpeg.Ct(term * (opA * term)^0) / foldBin,
  compexp = lpeg.Ct(addexp * (opComp * addexp)^0) / foldBin,
  andexp = lpeg.Ct(compexp * (Rw"and" * compexp)^0) / foldLog"and",
  exp = lpeg.Ct(andexp * (Rw"or" * andexp)^0) / foldLog"or",
  space = (lpeg.S(" \t\n") + comment)^0
            * lpeg.P(function (_,p)
                       maxmatch = math.max(maxmatch, p);
                       return true
                     end)
}


local function syntaxError (input, max)
  -- count newlines up to max
  local _, line = string.gsub(string.sub(input, 1, max), "\n", "")
  line = line + 1   -- first line is 1 (not 0)
  io.stderr:write("syntax error at line ", line, "\n")
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
             ["*"] = "mul", ["/"] = "div", ["%"] = "mod", ["^"] = "exp",
             [">="] = "ge", ["<="] = "le", ["=="] = "eq", ["!="] = "ne",
             [">"] = "gt", ["<"] = "lt",
            }

local unOps = {["-"] = "neg", ["!"] = "not1"}

local logOps = {["and"] = "jmpZP", ["or"] = "jmpNZP"}


function Compiler:var2num (id)
  local num = self.vars[id]
  if not num then   -- new variable?
    num = self.nvars + 1
    self.nvars = num
    self.vars[id] = num
  end
  return num
end


function Compiler:currentPosition ()
  return #self.code
end


function Compiler:fixJmp (label, jmp)
  self.code[jmp] = label  - jmp
end


function Compiler:codeJmpB (op, label)
  self:addCode(op)
  self:addCode(0)
  -- jump from here to 'label'
  self:fixJmp(label, self:currentPosition())
end


function Compiler:codeJmpF (op)
  self:addCode(op)
  self:addCode(0)
  return self:currentPosition()   -- position of the jump to be corrected
end


function Compiler:fixJmp2here (jmp)
  -- jump from 'jmp' to here
  self:fixJmp(self:currentPosition(), jmp)
end


function Compiler:codeExp (ast)
  if ast.tag == "number" then
    self:addCode("push")
    self:addCode(ast.val)
  elseif ast.tag == "unop" then
    self:codeExp(ast.e)
    self:addCode(unOps[ast.op])
  elseif ast.tag == "variable" then
    self:addCode("load")
    self:addCode(self:var2num(ast.var))
  elseif ast.tag == "binop" then
    self:codeExp(ast.e1)
    self:codeExp(ast.e2)
    self:addCode(ops[ast.op])
  elseif ast.tag == "logop" then
    self:codeExp(ast.e1)
    local jmp = self:codeJmpF(logOps[ast.op])
    self:codeExp(ast.e2)
    self:fixJmp2here(jmp)
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
  elseif ast.tag == "print" then
    self:codeExp(ast.exp)
    self:addCode("print")
  elseif ast.tag == "nop" then
    -- no operation, no code
  elseif ast.tag == "while1" then
    local ilabel = self:currentPosition()
    self:codeExp(ast.cond)
    local jmp = self:codeJmpF("jmpZ")
    self:codeStat(ast.body)
    self:codeJmpB("jmp", ilabel)
    self:fixJmp2here(jmp)
  elseif ast.tag == "if1" then
    self:codeExp(ast.cond)
    local jmp = self:codeJmpF("jmpZ")
    self:codeStat(ast.th)
    if ast.el == nil then
      self:fixJmp2here(jmp)
    else
      local jmp2 = self:codeJmpF("jmp")
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

-- convert boolean to integer
local function b2n (n) return n and 1 or 0 end

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
    elseif code[pc] == "neg" then
      stack[top] = -stack[top]
    elseif code[pc] == "not1" then
      stack[top] = (stack[top] == 0) and 1 or 0
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
    elseif code[pc] == "ge" then
      stack[top - 1] = b2n(stack[top - 1] >= stack[top])
      top = top - 1
    elseif code[pc] == "le" then
      stack[top - 1] = b2n(stack[top - 1] <= stack[top])
      top = top - 1
    elseif code[pc] == "eq" then
      stack[top - 1] = b2n(stack[top - 1] == stack[top])
      top = top - 1
    elseif code[pc] == "ne" then
      stack[top - 1] = b2n(stack[top - 1] ~= stack[top])
      top = top - 1
    elseif code[pc] == "gt" then
      stack[top - 1] = b2n(stack[top - 1] > stack[top])
      top = top - 1
    elseif code[pc] == "lt" then
      stack[top - 1] = b2n(stack[top - 1] < stack[top])
      top = top - 1
    elseif code[pc] == "print" then
      print(stack[top])
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
      pc = pc + 1
      pc = pc + code[pc]
    elseif code[pc] == "jmpZ" then
      pc = pc + 1
      if stack[top] == 0 then
        pc = pc + code[pc]
      end
      top = top - 1
    elseif code[pc] == "jmpZP" then
      pc = pc + 1
      if stack[top] == 0 then
        pc = pc + code[pc]
      else
        top = top - 1
      end
    elseif code[pc] == "jmpNZP" then
      pc = pc + 1
      if stack[top] ~= 0 then
        pc = pc + code[pc]
      else
        top = top - 1
      end
    else error("unknown instruction")
    end
    pc = pc + 1
  end
end


local input = io.read("a")
local ast = parse(input)
-- print(pt.pt(ast))
local code = compile(ast)
-- print(pt.pt(code))
local stack = {}
local mem = {}
run(code, mem, stack)
print(stack[1])
