// <vc-preamble>
function digitSum(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else (n % 10) + digitSum(n / 10)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added bound lemma to help prove termination and postconditions */
lemma BoundLemma(x: int, n: int)
  requires x > 0
  requires n > 1
  requires x * x >= n
  ensures forall y :: y >= x ==> y * y + digitSum(y) * y >= n
{
}

function maxSearchBound(n: int): int
  requires n > 1
  ensures maxSearchBound(n) > 0
  ensures maxSearchBound(n) * maxSearchBound(n) >= n
{
  var bound := 1;
  if bound * bound >= n then bound else n
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires n >= 1
  ensures n == 1 ==> result == -1
  ensures n > 1 && result > 0 ==> result * result + digitSum(result) * result == n
  ensures n > 1 && result > 0 ==> forall y :: y > 0 && y < result ==> y * y + digitSum(y) * y != n
  ensures n > 1 && result == -1 ==> forall x :: x > 0 ==> x * x + digitSum(x) * x != n
  ensures result == -1 || result > 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added decreases clause and stronger invariants for verification */
  if n == 1 {
    return -1;
  }
  
  var searchBound := maxSearchBound(n);
  var x := 1;
  
  while x * x + digitSum(x) * x < n
    invariant x >= 1
    invariant forall y :: 1 <= y < x ==> y * y + digitSum(y) * y < n
    invariant x <= searchBound + 1
    decreases searchBound + 1 - x
  {
    x := x + 1;
  }
  
  if x * x + digitSum(x) * x == n {
    return x;
  } else {
    assert x * x + digitSum(x) * x > n;
    assert forall y :: 1 <= y < x ==> y * y + digitSum(y) * y < n;
    assert forall y :: y >= x ==> y * y >= x * x > n - digitSum(x) * x;
    return -1;
  }
}
// </vc-code>
