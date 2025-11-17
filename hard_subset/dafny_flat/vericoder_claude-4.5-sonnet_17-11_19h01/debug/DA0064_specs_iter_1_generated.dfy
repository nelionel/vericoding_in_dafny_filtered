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
  var count := 0;
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant count == |set x | 1 <= x < i && Check(x, s)|
  {
    SumOfDigitsNonnegative(i);
    SumOfDigitsUpperBound(i);
    
    if Check(i, s) {
      count := count + 1;
    }
    
    i := i + 1;
  }
  
  result := count;
}
// </vc-code>
