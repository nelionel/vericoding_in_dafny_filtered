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
/* helper modified by LLM (iteration 3): Added lemma to establish relationship between power of 2 and string length */
lemma Pow2EquivalenceLemma(sy: string, n: nat)
  requires ValidBitString(sy)
  requires |sy| == n + 1
  requires sy[0] == '0'
  requires AllZero(sy[1..])
  ensures Str2Int(sy) == Exp_int(2, n) || Str2Int(sy) == 0
{
  if n == 0 {
    assert |sy| == 1;
    assert sy[0] == '0';
    assert Str2Int(sy) == 0;
  } else {
    assert Str2Int(sy) == 0;
  }
}

/* helper modified by LLM (iteration 3): Added lemma to prove zeros string satisfies AllZero */
lemma ZerosIsAllZero(s: string, n: nat)
  requires s == Zeros(n)
  ensures AllZero(s)
{
}

/* helper modified by LLM (iteration 3): Added lemma for base case verification */
lemma BaseCase(sx: string, sz: string)
  requires ValidBitString(sx) && ValidBitString(sz)
  requires Str2Int(sz) > 1
  ensures Str2Int(sx) == Exp_int(Str2Int(sx), 1) % Str2Int(sz)
{
  assert Exp_int(Str2Int(sx), 1) == Str2Int(sx) * Exp_int(Str2Int(sx), 0);
  assert Exp_int(Str2Int(sx), 0) == 1;
  assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
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
  /* code modified by LLM (iteration 3): Fixed to handle base case when |sy| == 1 and sy[0] == '1' */
  if |sy| == 1 {
    if sy[0] == '0' {
      res := "1";
    } else {
      res := sx;
    }
  } else if sy[0] == '0' {
    var zeros := Zeros(|sy| - 1);
    var sy_rest := "0" + zeros;
    ZerosIsAllZero(zeros, |sy| - 1);
    Pow2EquivalenceLemma(sy_rest, |sy| - 1);
    res := ModExpPow2(sx, sy_rest, |sy| - 1, sz);
  } else {
    var sy_rest := sy[1..];
    var rec_res := ModExp(sx, sy_rest, sz);
    res := rec_res;
  }
}
// </vc-code>
