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

method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)

  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
{
  assume{:axiom} false;
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
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
// </vc-preamble>

// <vc-helpers>
lemma ExpModDistributesOverSquare(base: nat, exp: nat, modulus: nat)
  requires modulus > 1
  ensures (Exp_int(base, exp) % modulus) * (Exp_int(base, exp) % modulus) % modulus == Exp_int(base, 2 * exp) % modulus
{
  calc {
    (Exp_int(base, exp) % modulus) * (Exp_int(base, exp) % modulus) % modulus;
    ==
    ((Exp_int(base, exp) * Exp_int(base, exp)) % modulus) % modulus;
    ==
    (Exp_int(base, exp) * Exp_int(base, exp)) % modulus;
    ==
    Exp_int(base, 2 * exp) % modulus;
  }
}

lemma ExpAdditive(base: nat, exp1: nat, exp2: nat)
  ensures Exp_int(base, exp1 + exp2) == Exp_int(base, exp1) * Exp_int(base, exp2)
{
}

lemma ModMulDistributes(a: nat, b: nat, m: nat)
  requires m > 1
  ensures (a % m) * (b % m) % m == (a * b) % m
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
  if sy == "0" {
    res := "1";
    return;
  }
  
  var lastBit := sy[|sy| - 1];
  var syPrime := sy[0..|sy| - 1];
  
  var recursiveResult := ModExp(sx, syPrime, sz);
  
  var squared := Mul(recursiveResult, recursiveResult);
  var quotient1, remainder1 := DivMod(squared, sz);
  
  if lastBit == '0' {
    res := remainder1;
  } else {
    var product := Mul(remainder1, sx);
    var quotient2, remainder2 := DivMod(product, sz);
    res := remainder2;
  }
}
// </vc-code>
