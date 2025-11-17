// <vc-preamble>
function ProductOfDigits(x: int): int
  requires x >= 0
{
  if x == 0 then 1
  else if x < 10 then x
  else (x % 10) * ProductOfDigits(x / 10)
}

function MaxProductOfDigitsInRange(n: int): int
  requires n >= 1
{
  if n == 1 then 1
  else
    var current := ProductOfDigits(n);
    var rest := MaxProductOfDigitsInRange(n - 1);
    if current > rest then current else rest
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires n >= 1
  ensures result == MaxProductOfDigitsInRange(n)
  ensures result >= 1
  ensures forall k :: 1 <= k <= n ==> ProductOfDigits(k) <= result
  ensures exists k :: 1 <= k <= n && ProductOfDigits(k) == result
// </vc-spec>
// <vc-code>
{
  result := 1;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant result >= 1
    invariant result == MaxProductOfDigitsInRange(i - 1)
    invariant forall k :: 1 <= k < i ==> ProductOfDigits(k) <= result
    invariant exists k :: 1 <= k < i && ProductOfDigits(k) == result
  {
    var current := ProductOfDigits(i);
    if current > result {
      result := current;
    }
    i := i + 1;
  }
}
// </vc-code>
