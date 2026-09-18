import LeanFzn
open LeanFzn.Lexer
#eval lexUnsigned (String.Internal.toArray "0x") 0          -- error: empty hex tail
#eval lexInt (String.Internal.toArray "0x") 0               -- error?
#eval lexInt (String.Internal.toArray "007") 0              -- octal? no — '0' then '0'.. check
#eval lexUnsigned (String.Internal.toArray "077") 0         -- 0 then 7: does the hex arm need 'x'? p+1='7' → not hex nor oct → decimal 77
#eval lexUnsigned (String.Internal.toArray "0o7") 0         -- octal 7
#eval lexInt (String.Internal.toArray "0o7") 0
