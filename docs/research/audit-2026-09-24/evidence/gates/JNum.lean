def jNum (x : Float) : String :=
  let neg := x < 0.0
  let a := if neg then -x else x
  let n : Nat := (a * 1.0e9 + 0.5).floor.toUInt64.toNat
  let intPart := n / 1000000000
  let frac := n % 1000000000
  let fs := toString frac
  let fracStr := String.ofList (List.replicate (9 - fs.length) '0') ++ fs
  (if neg then "-" else "") ++ toString intPart ++ "." ++ fracStr
#eval jNum (0.0/0.0)
#eval jNum (1.0/0.0)
#eval jNum (-1.0/0.0)
#eval jNum 1.6e12
#eval jNum 3.0e-10
#eval jNum (Float.log 0.0)
#eval jNum (Float.sqrt (-1.0))
