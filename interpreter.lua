local lpeg = require "lpeg"
local pt = require "pt"

local space = lpeg.S(" \n\t")^0
local numeral = (lpeg.R("09")^1 / tonumber) * space
local op = "+" * space


function fold (lst)
  local acc = lst[1]
  for i = 2, #lst do
      acc = acc + lst[i]
  end
  return acc
end


local sum = space * lpeg.Ct(numeral * (op * numeral)^0) / fold * -1

print(pt.pt(sum:match(" 12 + 32 + 14 + 90  ")))
