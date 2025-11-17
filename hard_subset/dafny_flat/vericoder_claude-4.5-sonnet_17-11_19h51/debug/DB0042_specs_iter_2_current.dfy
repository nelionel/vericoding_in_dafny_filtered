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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
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
/* helper modified by LLM (iteration 2): added lemmas to prove exponentiation properties and bit string relationships */
lemma ExpHalfSquared(x: nat, y: nat)
  ensures Exp_int(x, y * 2) == Exp_int(Exp_int(x, y), 2)
{
  if y == 0 {
  } else {
    calc {
      Exp_int(x, y * 2);
      ==
      x * Exp_int(x, y * 2 - 1);
      ==
      x * x * Exp_int(x, y * 2 - 2);
      ==
      Exp_int(x, 2) * Exp_int(x, y * 2 - 2);
    }
    ExpHalfSquared(x, y - 1);
  }
}

lemma Str2IntHalf(s: string)
  requires ValidBitString(s) && |s| > 0
  ensures Str2Int(s[0..|s|-1]) * 2 == Str2Int(s) - (if s[|s|-1] == '1' then 1 else 0)
{
}

lemma ExpDoubleY(x: nat, y: nat)
  ensures Exp_int(x, 2 * y) == Exp_int(Exp_int(x, y), 2)
{
  ExpHalfSquared(x, y);
}

lemma ExpOddY(x: nat, y: nat)
  requires y > 0
  ensures Exp_int(x, 2 * y + 1) == x * Exp_int(Exp_int(x, y), 2)
{
  calc {
    Exp_int(x, 2 * y + 1);
    ==
    x * Exp_int(x, 2 * y);
    == { ExpDoubleY(x, y); }
    x * Exp_int(Exp_int(x, y), 2);
  }
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
  /* code modified by LLM (iteration 2): handle base case with proper length check and add lemma calls for verification */
  if |sy| == 1 && sy[0] == '0' {
    res := "1";
    return;
  }
  
  if |sy| == 1 && sy[0] == '1' {
    var _, remainder := DivMod(sx, sz);
    res := remainder;
    return;
  }
  
  var half_y := sy[0..|sy|-1];
  var last_bit := sy[|sy|-1];
  
  Str2IntHalf(sy);
  
  var half_res := ModExp(sx, half_y, sz);
  var squared := Mul(half_res, half_res);
  var _, sq_mod := DivMod(squared, sz);
  
  if last_bit == '0' {
    ExpDoubleY(Str2Int(sx), Str2Int(half_y));
    res := sq_mod;
  } else {
    ExpOddY(Str2Int(sx), Str2Int(half_y));
    var temp := Mul(sq_mod, sx);
    var _, final_mod := DivMod(temp, sz);
    res := final_mod;
  }
}
// </vc-code>
