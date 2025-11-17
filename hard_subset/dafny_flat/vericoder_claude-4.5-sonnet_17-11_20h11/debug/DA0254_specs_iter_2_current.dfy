// <vc-preamble>
predicate ValidInput(n: int, k: int, L: seq<int>)
{
  n >= 1 && k >= 1 && |L| == n && k <= n * (n + 1) / 2
}

function TotalIdentifiersAfterRobot(i: int): int
  requires i >= 0
{
  i * (i + 1) / 2
}

predicate CorrectResult(n: int, k: int, L: seq<int>, result: int)
  requires ValidInput(n, k, L)
{
  exists i :: 1 <= i <= n && 
    TotalIdentifiersAfterRobot(i - 1) < k <= TotalIdentifiersAfterRobot(i) &&
    result == L[k - TotalIdentifiersAfterRobot(i - 1) - 1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added lemma to prove index bounds */
lemma IndexInBounds(n: int, k: int, L: seq<int>, i: int)
  requires ValidInput(n, k, L)
  requires 1 <= i <= n
  requires TotalIdentifiersAfterRobot(i - 1) < k <= TotalIdentifiersAfterRobot(i)
  ensures 0 <= k - TotalIdentifiersAfterRobot(i - 1) - 1 < |L|
{
  assert k - TotalIdentifiersAfterRobot(i - 1) - 1 >= 0;
  assert TotalIdentifiersAfterRobot(i - 1) >= 0;
  assert k <= TotalIdentifiersAfterRobot(i);
  assert TotalIdentifiersAfterRobot(i) == i * (i + 1) / 2;
  assert i <= n;
  assert k - TotalIdentifiersAfterRobot(i - 1) - 1 < i;
  assert i <= n;
  assert k - TotalIdentifiersAfterRobot(i - 1) - 1 < n;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, L: seq<int>) returns (result: int)
  requires ValidInput(n, k, L)
  ensures CorrectResult(n, k, L, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added index bounds proof */
  var i := 1;
  var totalBefore := 0;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant totalBefore == TotalIdentifiersAfterRobot(i - 1)
    invariant k > totalBefore
  {
    var totalAfter := TotalIdentifiersAfterRobot(i);
    if k <= totalAfter {
      IndexInBounds(n, k, L, i);
      result := L[k - totalBefore - 1];
      return;
    }
    i := i + 1;
    totalBefore := totalAfter;
  }
}
// </vc-code>
