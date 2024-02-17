module RDL::Type
class Parser

macro
  ID ((\w|\:\:)+(!|\?|=)?)|~|\+|-|\/|&|\||\^
  SYMBOL :\w+
  SPECIAL_ID %\w+
  FIXNUM -?(\d)+
  FLOAT -?\d\.\d+
  PREDICATE \{\{(?:(?!}}).)+\}\}
  COMP  ``(?:(?!``).)+``
  EFF \\


rule
  \s            # skip
  ->            { [:RARROW, text] }
  =>            { [:RASSOC, text] }
  \(            { [:LPAREN, text] }
  \)            { [:RPAREN, text] }
  {PREDICATE}   { [:PREDICATE, text[2..-3]] }
  \{            { [:LBRACE, text] }
  \}            { [:RBRACE, text] }
  \[            { [:LBRACKET, text] }
  \]            { [:RBRACKET, text] }
  <\:\:		{ [:BIND, text] }
  <             { [:LESS, text] }
  >             { [:GREATER, text] }
  =             { [:EQUAL, text] }
  ,             { [:COMMA, text] }
  \?            { [:QUERY, text] }
  \!            { [:BANG, text] }
  ~             { [:TILDE, text] }
  \*\*          { [:STARSTAR, text] }
  \*            { [:STAR, text] }
  \#T           { [:HASH_TYPE, text] }
  \#Q           { [:HASH_QUERY, text] }
  \$\{          { [:CONST_BEGIN, text] }
  \.\.\.        { [:DOTS, text] }
  \.            { [:DOT, text] }
  {COMP}	      { [:COMP, text[2..-3]] }
  {FLOAT}       { [:FLOAT, text] } # Must go before FIXNUM
  {FIXNUM}      { [:FIXNUM, text] }
  {ID}          { if text == "or" then [:OR, text] else [:ID, text] end }
  {SYMBOL}      { [:SYMBOL, text[1..-1]] }
  \:            { [:COLON, text] } # Must come after SYMBOL
  {SPECIAL_ID}  { [:SPECIAL_ID, text] }
  '[^']*'       { [:STRING, text.gsub("'", "")] }
  "[^"]*"       { [:STRING, text.gsub('"', "")] }

end
end
