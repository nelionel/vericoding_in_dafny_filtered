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
/* helper modified by LLM (iteration 3): adds bound function for termination */
function computeValue(x: int): int
  requires x >= 0
{
  x * x + digitSum(x) * x
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
  /* code modified by LLM (iteration 3): fixed loop invariant to hold on entry */
  if n == 1 {
    return -1;
  }
  
  var x := 1;
  var upperBound := n;
  
  while x < upperBound && x * x + digitSum(x) * x < n
    invariant x >= 1
    invariant forall y :: 1 <= y < x ==> y * y + digitSum(y) * y != n
    invariant x >= upperBound || x * x + digitSum(x) * x < n
    decreases upperBound - x
  {
    x := x + 1;
  }
  
  if x < upperBound && x * x + digitSum(x) * x == n {
    return x;
  } else {
    assert forall y :: 1 <= y < upperBound ==> y * y + digitSum(y) * y != n;
    return -1;
  }
}
// </vc-code>
