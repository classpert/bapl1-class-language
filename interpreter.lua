
local lpeg = require "lpeg"
local pt = require "pt"

local space = lpeg.S(" \n\t")^0
local numeral = (lpeg.R("09")^1 / tonumber) * space
local opA = lpeg.C(lpeg.S"+-") * space
local opM = lpeg.C(lpeg.S"*/") * space

local OP = "(" * space
local CP = ")" * space

function fold (lst)
  local acc = lst[1]
  for i = 2, #lst, 2 do
    if lst[i] == "+" then
      acc = acc + lst[i + 1]
    elseif lst[i] == "-" then
      acc = acc - lst[i + 1]
    elseif lst[i] == "*" then
      acc = acc * lst[i + 1]
    elseif lst[i] == "/" then
      acc = acc / lst[i + 1]
    else
      error("unknown operator")
    end
  end
  return acc
end


local primary = lpeg.V"primary"
local term = lpeg.V"term"
local exp = lpeg.V"exp"

g = lpeg.P{"exp",
  primary = numeral + OP * exp * CP,
  term = space * lpeg.Ct(primary * (opM * primary)^0) / fold,
  exp = space * lpeg.Ct(term * (opA * term)^0) / fold
}

g = g * -1

local subject = "2 * (2 + 4) * 10"
print(subject)
print(pt.pt(g:match(subject)))
