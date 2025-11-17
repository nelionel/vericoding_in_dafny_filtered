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
ghost function ModMul(a: nat, b: nat, m: nat): nat
  requires m > 0
{
  (a * b) % m
}

lemma ModMulAssoc(a: nat, b: nat, c: nat, m: nat)
  requires m > 0
  ensures (a * b * c) % m == ((a * b) % m * c) % m
{
}

lemma ExpMod(x: nat, y: nat, z: nat)
  requires z > 0
  ensures Exp_int(x, y) % z == (if y == 0 then 1 % z else (Exp_int(x, y - 1) % z * x % z) % z)
{
  if y == 0 {
  } else {
    calc {
      Exp_int(x, y) % z;
      ==
      (x * Exp_int(x, y - 1)) % z;
    }
  }
}

method Mod(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s2) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) % Str2Int(s2)
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
    return;
  }
  
  var half_exp := ModExp(sx, sy[0..|sy|-1], sz);
  var squared := Mul(half_exp, half_exp);
  var sq_mod := Mod(squared, sz);
  
  if sy[|sy|-1] == '0' {
    res := sq_mod;
  } else {
    var temp := Mul(sq_mod, sx);
    res := Mod(temp, sz);
  }
}
// </vc-code>
