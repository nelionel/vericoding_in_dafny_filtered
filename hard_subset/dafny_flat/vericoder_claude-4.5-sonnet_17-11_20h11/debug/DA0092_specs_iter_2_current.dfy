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
/* helper modified by LLM (iteration 2): Fixed witness construction in MaxProductProperty */
lemma MaxProductProperty(n: int, maxSoFar: int)
  requires n >= 1
  requires maxSoFar == MaxProductOfDigitsInRange(n)
  ensures forall k :: 1 <= k <= n ==> ProductOfDigits(k) <= maxSoFar
  ensures exists k :: 1 <= k <= n && ProductOfDigits(k) == maxSoFar
{
  if n == 1 {
    assert ProductOfDigits(1) == 1;
    assert maxSoFar == 1;
  } else {
    var current := ProductOfDigits(n);
    var rest := MaxProductOfDigitsInRange(n - 1);
    MaxProductProperty(n - 1, rest);
    if current > rest {
      assert maxSoFar == current;
      assert ProductOfDigits(n) == maxSoFar;
    } else {
      assert maxSoFar == rest;
      var k :| 1 <= k <= n - 1 && ProductOfDigits(k) == rest;
      assert ProductOfDigits(k) == maxSoFar;
    }
  }
}

lemma ProductOfDigitsPositive(x: int)
  requires x >= 0
  ensures ProductOfDigits(x) >= 1
{
  if x == 0 {
  } else if x < 10 {
  } else {
    ProductOfDigitsPositive(x / 10);
  }
}

lemma MaxProductPositive(n: int)
  requires n >= 1
  ensures MaxProductOfDigitsInRange(n) >= 1
{
  if n == 1 {
  } else {
    ProductOfDigitsPositive(n);
    MaxProductPositive(n - 1);
  }
}
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
  /* code modified by LLM (iteration 2): Fixed loop invariant to handle i=1 case and iterative computation */
  result := 1;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant i > 1 ==> result == MaxProductOfDigitsInRange(i - 1)
    invariant i == 1 ==> result == 1
  {
    var prod := ProductOfDigits(i);
    if i == 1 {
      result := prod;
    } else if prod > result {
      result := prod;
    }
    assert result == MaxProductOfDigitsInRange(i);
    i := i + 1;
  }
  MaxProductProperty(n, result);
  MaxProductPositive(n);
}
// </vc-code>
