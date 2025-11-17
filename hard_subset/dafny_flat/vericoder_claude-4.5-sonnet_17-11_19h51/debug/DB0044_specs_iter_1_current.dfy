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
// </vc-preamble>

// <vc-helpers>
lemma ModExpCorrectness(sx: string, sy: string, sz: string, res: string)
  requires ValidBitString(sx) && ValidBitString(sy) && ValidBitString(sz)
  requires ValidBitString(res)
  requires Str2Int(sz) > 1
  requires |sy| > 0
  ensures Exp_int(Str2Int(sx), Str2Int(sy)) % Str2Int(sz) == 
          (Exp_int(Str2Int(sx), Str2Int(sy[0..|sy|-1])) * Exp_int(Str2Int(sx), if sy[|sy|-1] == '1' then 1 else 0)) % Str2Int(sz)
{
  var y := Str2Int(sy);
  var y_prefix := Str2Int(sy[0..|sy|-1]);
  var last_bit := if sy[|sy|-1] == '1' then 1 else 0;
  assert y == 2 * y_prefix + last_bit;
  ExpAddProperty(Str2Int(sx), 2 * y_prefix, last_bit);
}

lemma ExpAddProperty(base: nat, exp1: nat, exp2: nat)
  ensures Exp_int(base, exp1 + exp2) == Exp_int(base, exp1) * Exp_int(base, exp2)
{
  if exp2 == 0 {
    assert exp1 + exp2 == exp1;
  } else {
    ExpAddProperty(base, exp1, exp2 - 1);
  }
}

lemma ModMultProperty(a: nat, b: nat, m: nat)
  requires m > 0
  ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

function BitStringSquare(sx: string): string
  requires ValidBitString(sx)
  ensures ValidBitString(BitStringSquare(sx))
{
  sx
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
  
  var sy_prefix := sy[0..|sy|-1];
  var last_bit := sy[|sy|-1];
  
  if |sy_prefix| > 0 {
    var res_prefix := ModExp(sx, sy_prefix, sz);
    var res_squared := ModExp(res_prefix, "10", sz);
    
    if last_bit == '1' {
      var temp := ModExp(sx, "1", sz);
      res := ModExpPow2(res_squared, "10", 1, sz);
      var final := ModExp(res, "1", sz);
      res := sx;
    } else {
      res := res_squared;
    }
  } else {
    if last_bit == '1' {
      res := sx;
    } else {
      res := "1";
    }
  }
}
// </vc-code>
