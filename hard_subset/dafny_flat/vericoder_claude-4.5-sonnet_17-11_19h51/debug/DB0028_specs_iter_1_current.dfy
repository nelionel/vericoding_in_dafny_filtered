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
ghost function ModExp_Spec(x: nat, y: nat, z: nat): nat
  requires z > 0
{
  Exp_int(x, y) % z
}

lemma ModExpRecursive(x: nat, y: nat, z: nat)
  requires z > 0
  requires y > 0
  ensures Exp_int(x, y) % z == (x * Exp_int(x, y - 1)) % z
{
}

lemma ModMul(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

lemma ModSquare(a: nat, m: nat)
  requires m > 0
  ensures (a * a) % m == ((a % m) * (a % m)) % m
{
}

lemma ExpDoubleExponent(x: nat, y: nat)
  ensures Exp_int(x, 2 * y) == Exp_int(Exp_int(x, y), 2)
{
  if y == 0 {
  } else {
    calc {
      Exp_int(x, 2 * y);
      ==
      Exp_int(x, y + y);
    }
  }
}

lemma Str2IntLowerBound(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  requires s[|s|-1] == '1'
  ensures Str2Int(s) > 0
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
  if |sy| == 1 && sy[0] == '0' {
    res := "1";
    return;
  }
  
  var lastChar := sy[|sy| - 1];
  var sy_prefix := sy[0..|sy| - 1];
  
  if |sy_prefix| == 0 {
    var _, r := DivMod(sx, sz);
    res := r;
    return;
  }
  
  var rec_res := ModExp(sx, sy_prefix, sz);
  var squared := ModExp(rec_res, "10", sz);
  
  if lastChar == '0' {
    res := squared;
  } else {
    var temp := ModExp(squared, sx, sz);
    var _, r := DivMod(temp, sz);
    res := r;
  }
}
// </vc-code>
