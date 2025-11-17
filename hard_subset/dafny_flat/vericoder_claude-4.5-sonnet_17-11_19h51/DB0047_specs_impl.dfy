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
/* helper modified by LLM (iteration 3): added modular arithmetic lemmas to prove postcondition */
lemma Exp_int_zero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma Str2Int_Zeros(n: nat, s: string)
  requires |s| == n
  requires ValidBitString(s)
  requires AllZero(s)
  ensures Str2Int(s) == 0
  decreases |s|
{
  if |s| == 0 {
  } else {
    assert s[|s|-1] == '0';
    Str2Int_Zeros(n-1, s[0..|s|-1]);
  }
}

lemma Str2Int_single_zero()
  ensures Str2Int("0") == 0
{
}

lemma Str2Int_single_one()
  ensures Str2Int("1") == 1
{
}

lemma ModMul(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

lemma Exp_int_double(x: nat, y: nat)
  ensures Exp_int(x, 2 * y) == Exp_int(Exp_int(x, y), 2)
  decreases y
{
  if y == 0 {
  } else {
    Exp_int_double(x, y - 1);
  }
}

lemma Exp_int_add(x: nat, y1: nat, y2: nat)
  ensures Exp_int(x, y1 + y2) == Exp_int(x, y1) * Exp_int(x, y2)
  decreases y1
{
  if y1 == 0 {
  } else {
    Exp_int_add(x, y1 - 1, y2);
  }
}

lemma Str2Int_recursive_property(s: string)
  requires ValidBitString(s)
  requires |s| > 0
  ensures Str2Int(s) == 2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0)
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
/* code modified by LLM (iteration 3): added modular arithmetic reasoning and lemma calls */
{
  if |sy| == 1 && sy[0] == '0' {
    Str2Int_single_zero();
    Exp_int_zero(Str2Int(sx));
    res := "1";
  } else if |sy| == 1 && sy[0] == '1' {
    Str2Int_single_one();
    res := sx;
  } else {
    var sy_prefix := sy[0..|sy|-1];
    assert |sy_prefix| > 0;
    var rec_res := ModExp(sx, sy_prefix, sz);
    var squared := Mul(rec_res, rec_res);
    
    Str2Int_recursive_property(sy);
    var sy_val := Str2Int(sy);
    var sy_prefix_val := Str2Int(sy_prefix);
    assert sy_val == 2 * sy_prefix_val + (if sy[|sy|-1] == '1' then 1 else 0);
    
    Exp_int_add(Str2Int(sx), sy_prefix_val, sy_prefix_val);
    
    if sy[|sy|-1] == '1' {
      Exp_int_add(Str2Int(sx), 2 * sy_prefix_val, 1);
      var temp := Mul(squared, sx);
      ModMul(Exp_int(Str2Int(sx), sy_prefix_val), Exp_int(Str2Int(sx), sy_prefix_val), Str2Int(sz));
      ModMul(Str2Int(squared), Str2Int(sx), Str2Int(sz));
      res := temp;
    } else {
      ModMul(Exp_int(Str2Int(sx), sy_prefix_val), Exp_int(Str2Int(sx), sy_prefix_val), Str2Int(sz));
      res := squared;
    }
  }
}
// </vc-code>
