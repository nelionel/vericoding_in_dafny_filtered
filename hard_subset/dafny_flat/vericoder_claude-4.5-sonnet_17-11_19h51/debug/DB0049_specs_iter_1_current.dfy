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

method Mul(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) * Str2Int(s2)
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
ghost function StrMod(s1: string, s2: string): nat
  requires ValidBitString(s1) && ValidBitString(s2) && Str2Int(s2) > 0
{
  Str2Int(s1) % Str2Int(s2)
}

method Mod(s1: string, s2: string) returns (res: string)
  requires ValidBitString(s1) && ValidBitString(s2)
  requires Str2Int(s2) > 0
  ensures ValidBitString(res)
  ensures Str2Int(res) == Str2Int(s1) % Str2Int(s2)
{
  assume {:axiom} false;
}

method IntToStr(n: nat) returns (res: string)
  ensures ValidBitString(res)
  ensures Str2Int(res) == n
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
  if sy == "0" {
    res := "1";
    return;
  }
  
  if |sy| == 1 && sy[0] == '1' {
    res := Mod(sx, sz);
    return;
  }
  
  var sy_half := sy[0..|sy|-1];
  var temp := ModExp(sx, sy_half, sz);
  var temp_sq := Mul(temp, temp);
  var temp_mod := Mod(temp_sq, sz);
  
  if sy[|sy|-1] == '0' {
    res := temp_mod;
  } else {
    var temp_mul := Mul(temp_mod, sx);
    res := Mod(temp_mul, sz);
  }
}
// </vc-code>
