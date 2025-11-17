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
/* helper modified by LLM (iteration 3): removed lemmas that call methods, added helper functions for string operations */
function ZeroString(n: nat): string
{
  if n == 0 then "" else ZeroString(n - 1) + "0"
}

lemma ZeroStringValid(n: nat)
  ensures ValidBitString(ZeroString(n))
  ensures |ZeroString(n)| == n
  ensures AllZero(ZeroString(n))
{
}

lemma ZeroStringValue(n: nat)
  ensures Str2Int(ZeroString(n)) == 0
  decreases n
{
  if n == 0 {
  } else {
    ZeroStringValue(n - 1);
  }
}

lemma ModExpBase(sx: string, sz: string)
  requires ValidBitString(sx) && ValidBitString(sz)
  requires Str2Int(sz) > 1
  ensures Exp_int(Str2Int(sx), 0) % Str2Int(sz) == 1
{
}

lemma Str2IntEmpty()
  ensures Str2Int("") == 0
{
}

function GetLastChar(s: string): char
  requires |s| > 0
{
  s[|s|-1]
}

function RemoveLastChar(s: string): string
  requires |s| > 0
  ensures |RemoveLastChar(s)| == |s| - 1
{
  s[0..|s|-1]
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
  /* code modified by LLM (iteration 3): basic implementation with base case handling */
  if |sy| == 1 && sy[0] == '0' {
    res := "1";
    assert Str2Int(sy) == 0;
    ModExpBase(sx, sz);
    return;
  }
  
  var sy_prefix := RemoveLastChar(sy);
  var last_bit := GetLastChar(sy);
  
  var rec_res := ModExp(sx, sy_prefix, sz);
  
  res := rec_res;
}
// </vc-code>
