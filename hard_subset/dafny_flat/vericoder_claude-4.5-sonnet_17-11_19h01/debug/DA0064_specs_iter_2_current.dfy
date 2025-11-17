// <vc-preamble>
function SumOfDigits(x: int): int
  requires x >= 0
  decreases x
{
  if x == 0 then 0
  else (x % 10) + SumOfDigits(x / 10)
}

function Check(x: int, s: int): bool
  requires x >= 0
{
  x - SumOfDigits(x) >= s
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added lemmas for reasoning about set cardinality */
lemma SumOfDigitsNonnegative(x: int)
  requires x >= 0
  ensures SumOfDigits(x) >= 0
  decreases x
{
  if x == 0 {
  } else {
    SumOfDigitsNonnegative(x / 10);
  }
}

lemma SumOfDigitsUpperBound(x: int)
  requires x >= 0
  ensures SumOfDigits(x) <= x
  decreases x
{
  if x == 0 {
  } else {
    SumOfDigitsUpperBound(x / 10);
  }
}

lemma SetExtension(n: int, s: int, i: int)
  requires 1 <= i <= n
  ensures set x | 1 <= x <= i && Check(x, s) == (set x | 1 <= x < i && Check(x, s)) + (if Check(i, s) then {i} else {})
{
}

lemma CardinalityBound(n: int, s: int)
  requires n >= 1
  ensures |set x | 1 <= x <= n && Check(x, s)| <= n
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: int) returns (result: int)
  requires n >= 1 && s >= 1
  ensures result >= 0
  ensures result <= n
  ensures result == |set x | 1 <= x <= n && Check(x, s)|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed loop invariant to maintain count relationship and added assertions */
  var count := 0;
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant count >= 0
    invariant count == |set x | 1 <= x < i && Check(x, s)|
    invariant count < i
  {
    SumOfDigitsNonnegative(i);
    SumOfDigitsUpperBound(i);
    
    ghost var oldSet := set x | 1 <= x < i && Check(x, s);
    SetExtension(n, s, i);
    
    if Check(i, s) {
      count := count + 1;
      assert count == |set x | 1 <= x <= i && Check(x, s)|;
    } else {
      assert count == |set x | 1 <= x <= i && Check(x, s)|;
    }
    
    i := i + 1;
  }
  
  CardinalityBound(n, s);
  result := count;
}
// </vc-code>
