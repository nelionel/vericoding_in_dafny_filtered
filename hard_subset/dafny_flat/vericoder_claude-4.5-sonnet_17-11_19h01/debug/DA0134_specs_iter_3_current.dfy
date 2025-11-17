// <vc-preamble>
predicate ValidInput(n: int, k: int)
{
    n >= 1 && k > 0
}

predicate IsCorrectResult(n: int, k: int, result: int)
    requires k > 0
{
    result > n && result % k == 0 && forall x :: n < x < result ==> x % k != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires ValidInput(n, k)
    ensures IsCorrectResult(n, k, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): simplified loop without decreases clause */
  var candidate := n + 1;
  while candidate % k != 0
    invariant candidate > n
    invariant forall x :: n < x < candidate ==> x % k != 0
  {
    candidate := candidate + 1;
  }
  result := candidate;
}
// </vc-code>
