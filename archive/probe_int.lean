import LeanFzn
open LeanFzn.Lexer
-- does lexUnsigned take the whole digit run on '12 3'-like input?
#eval lexUnsigned (String.Internal.toArray "12") 0        -- expect ok (12, 2)
#eval lexUnsigned (String.Internal.toArray "12 ") 0       -- expect ok (12, 2)
#eval lexUnsigned (String.Internal.toArray "0xab") 0
#eval lexInt (String.Internal.toArray "-12") 0
#eval takeWhile isDigit (String.Internal.toArray "12") 0 ""
