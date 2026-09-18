import LeanFzn
open LeanFzn.Lexer
#eval lexUnsigned (String.Internal.toArray "10") 0   -- '1','0': p+1='0' not x/o → decimal 10
#eval lexUnsigned (String.Internal.toArray "0o") 0   -- octal error
#eval lexInt (String.Internal.toArray "0o") 0
#eval parseDecNat "0"
#eval parseDecNat "12"
