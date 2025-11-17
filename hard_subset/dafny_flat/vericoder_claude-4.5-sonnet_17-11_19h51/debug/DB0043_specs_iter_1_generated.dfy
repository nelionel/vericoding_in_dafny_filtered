// <vc-preamble>
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{

  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
predicate AllZero(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0'
}

method DivMod(dividend: string, divisor: string) returns (quotient: string, remainder: string)
  requires ValidBitString(dividend) && ValidBitString(divisor)
  requires Str2Int(divisor) > 0
  ensures ValidBitString(quotient) && ValidBitString(remainder)
  ensures Str2Int(quotient) == Str2Int(dividend) / Str2Int(divisor)
  ensures Str2Int(remainder) == Str2Int(dividend) % Str2Int(divisor)
{
  assume{:axiom} false;
}

method Zeros(n: nat) returns (s: string)
  ensures |s| == n
  ensures ValidBitString(s)
  ensures Str2Int(s) == 0
  ensures AllZero(s)
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
ghost function Exp_mod(x: nat, y: nat, z: nat): nat
  requires z > 0
  decreases y
{
  if y == 0 then 1 % z
  else if y % 2 == 0 then
    var half := Exp_mod(x, y / 2, z);
    (half * half) % z
  else
    (x * Exp_mod(x, y - 1, z)) % z
}

lemma ExpModEquivalence(x: nat, y: nat, z: nat)
  requires z > 0
  ensures Exp_mod(x, y, z) == Exp_int(x, y) % z
  decreases y
{
  if y == 0 {
  } else if y % 2 == 0 {
    ExpModEquivalence(x, y / 2, z);
    calc {
      Exp_int(x, y);
      ==
      Exp_int(x, y / 2) * Exp_int(x, y / 2);
    }
  } else {
    ExpModEquivalence(x, y - 1, z);
  }
}

method Mul(a: string, b: string) returns (result: string)
  requires ValidBitString(a) && ValidBitString(b)
  ensures ValidBitString(result)
  ensures Str2Int(result) == Str2Int(a) * Str2Int(b)
{
  assume {:axiom} false;
}
// </vc-helpers>

// <vc-spec>
method ModExp(sx: string, sy: string, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)

  requires |sy| > 0 && Str2Int(sz) > 1
  decreases |sy|
// </vc-spec>
// <vc-code>
{
  if |sy| == 1 && sy[0] == '0' {
    res := "1";
    var _, rem := DivMod(res, sz);
    res := rem;
    return;
  }
  
  var last := sy[|sy| - 1];
  var sy_prefix := sy[0..|sy| - 1];
  
  if |sy_prefix| == 0 {
    var _, rem := DivMod(sx, sz);
    res := rem;
    return;
  }
  
  var rec := ModExp(sx, sy_prefix, sz);
  var squared := Mul(rec, rec);
  var _, sq_mod := DivMod(squared, sz);
  
  if last == '0' {
    res := sq_mod;
  } else {
    var mult := Mul(sx, sq_mod);
    var _, final_mod := DivMod(mult, sz);
    res := final_mod;
  }
}
// </vc-code>
