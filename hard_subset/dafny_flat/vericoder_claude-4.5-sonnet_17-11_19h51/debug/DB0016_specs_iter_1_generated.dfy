// <vc-preamble>
ghost function Exp_int(x: nat, y:nat): nat
{
  if y == 0 then 1 else x * Exp_int(x, y - 1)
}
predicate ValidBitString(s: string)
{

  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}
ghost function Str2Int(s: string): nat
  requires ValidBitString(s)
  decreases s
{
  if |s| == 0 then  0  else  (2 * Str2Int(s[0..|s|-1]) + (if s[|s|-1] == '1' then 1 else 0))
}

method Add(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) + Str2Int(s2)
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
lemma Exp_int_zero(x: nat)
  ensures Exp_int(x, 0) == 1
{
}

lemma Exp_int_double(x: nat, y: nat)
  ensures Exp_int(x, 2 * y) == Exp_int(Exp_int(x, y), 2)
{
  if y == 0 {
    assert Exp_int(x, 0) == 1;
    assert Exp_int(1, 2) == 1;
  } else {
    calc {
      Exp_int(x, 2 * y);
      ==
      Exp_int(x, y + y);
      ==
      { Exp_int_add(x, y, y); }
      Exp_int(x, y) * Exp_int(x, y);
      ==
      Exp_int(Exp_int(x, y), 2);
    }
  }
}

lemma Exp_int_add(x: nat, y: nat, z: nat)
  ensures Exp_int(x, y + z) == Exp_int(x, y) * Exp_int(x, z)
{
  if z == 0 {
    assert Exp_int(x, z) == 1;
  } else {
    calc {
      Exp_int(x, y + z);
      ==
      x * Exp_int(x, y + z - 1);
      ==
      { Exp_int_add(x, y, z - 1); }
      x * Exp_int(x, y) * Exp_int(x, z - 1);
      ==
      Exp_int(x, y) * (x * Exp_int(x, z - 1));
      ==
      Exp_int(x, y) * Exp_int(x, z);
    }
  }
}

lemma Exp_int_power_of_two(n: nat)
  ensures Exp_int(2, n) > 0
{
}

lemma ModMulProperty(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}
// </vc-helpers>

// <vc-spec>
method ModExpPow2(sx: string, sy: string, n: nat, sz: string) returns (res: string)
  requires ValidBitString(sx) && ValidBitString(sy) &&  ValidBitString(sz)

  requires Str2Int(sy) == Exp_int(2,n) || Str2Int(sy) == 0
  requires |sy| == n+1
  requires Str2Int(sz) > 1
  ensures ValidBitString(res)
  ensures Str2Int(res) == Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz)
  decreases n
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    if Str2Int(sy) == 0 {
      res := "1";
      Exp_int_zero(Str2Int(sx));
      return;
    } else {
      res := Mul(sx, "1");
      assert Str2Int(sy) == 1;
      assert Exp_int(Str2Int(sx), 1) == Str2Int(sx);
      return;
    }
  } else {
    if Str2Int(sy) == 0 {
      res := "1";
      Exp_int_zero(Str2Int(sx));
      return;
    } else {
      assert Str2Int(sy) == Exp_int(2, n);
      var sy_half := sy[0..n];
      assert |sy_half| == n;
      
      var rec_res := ModExpPow2(sx, sy_half, n - 1, sz);
      var squared := Mul(rec_res, rec_res);
      res := Mul(squared, "1");
      
      return;
    }
  }
}
// </vc-code>
