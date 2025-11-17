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

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  assume{:axiom} false;
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added lemmas to prove modular exponentiation properties */
lemma ExpDoubleProperty(x: nat, y: nat)
  ensures Exp_int(x, 2 * y) == Exp_int(Exp_int(x, y), 2)
{
  if y == 0 {
  } else {
    calc {
      Exp_int(x, 2 * y);
      ==
      x * Exp_int(x, 2 * y - 1);
      ==
      x * x * Exp_int(x, 2 * y - 2);
    }
  }
}

lemma ExpAddProperty(x: nat, y: nat)
  ensures y > 0 ==> Exp_int(x, y) == x * Exp_int(x, y - 1)
{
}

lemma ModMulProperty(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

lemma ExpHalfProperty(x: nat, y: nat)
  requires y > 0
  ensures Exp_int(x, y) == (if y % 2 == 0 then Exp_int(Exp_int(x, y / 2), 2) else x * Exp_int(Exp_int(x, y / 2), 2))
{
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
  /* code modified by LLM (iteration 2): handle base case properly and ensure preconditions for recursive call */
  if sy == "0" {
    res := "1";
    return;
  }
  
  var last_bit := sy[|sy|-1];
  var sy_prefix := sy[0..|sy|-1];
  
  if |sy_prefix| == 0 {
    if last_bit == '0' {
      res := "1";
    } else {
      var _, rem := DivMod(sx, sz);
      res := rem;
    }
    return;
  }
  
  var rec_res := ModExp(sx, sy_prefix, sz);
  
  var temp1 := Add(rec_res, rec_res);
  var _, squared := DivMod(temp1, sz);
  
  if last_bit == '0' {
    res := squared;
  } else {
    var temp2 := Add(squared, sx);
    var _, rem2 := DivMod(temp2, sz);
    res := rem2;
  }
}
// </vc-code>
