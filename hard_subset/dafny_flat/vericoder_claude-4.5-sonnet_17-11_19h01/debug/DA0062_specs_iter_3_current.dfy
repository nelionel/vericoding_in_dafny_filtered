// <vc-preamble>
predicate ValidInput(n: int)
{
    n >= 1
}

function vasya_eats_with_strategy(n: int, k: int): int
    requires n >= 0
    requires k >= 1
    decreases n
{
    if n <= 0 then 0
    else
        var cur := if n < k then n else k;
        var remaining_after_vasya := n - cur;
        var remaining_after_petya := remaining_after_vasya - remaining_after_vasya / 10;
        cur + vasya_eats_with_strategy(remaining_after_petya, k)
}

predicate IsMinimalSolution(n: int, k: int)
    requires ValidInput(n)
    requires k >= 1
{
    vasya_eats_with_strategy(n, k) * 2 >= n &&
    (k == 1 || vasya_eats_with_strategy(n, k - 1) * 2 < n)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed monotonicity lemma and base case lemma */
lemma VasyaEatsMonotonic(n: int, k1: int, k2: int)
  requires n >= 0
  requires k1 >= 1 && k2 >= 1
  requires k1 <= k2
  ensures vasya_eats_with_strategy(n, k1) <= vasya_eats_with_strategy(n, k2)
  decreases n
{
  if n <= 0 {
  } else {
    var cur1 := if n < k1 then n else k1;
    var remaining_after_vasya1 := n - cur1;
    var remaining_after_petya1 := remaining_after_vasya1 - remaining_after_vasya1 / 10;
    var cur2 := if n < k2 then n else k2;
    var remaining_after_vasya2 := n - cur2;
    var remaining_after_petya2 := remaining_after_vasya2 - remaining_after_vasya2 / 10;
    if remaining_after_petya1 > 0 {
      VasyaEatsMonotonic(remaining_after_petya1, k1, k2);
    }
    if remaining_after_petya2 > 0 {
      VasyaEatsMonotonic(remaining_after_petya2, k1, k2);
    }
  }
}

lemma VasyaEatsAtLeastHalfAtN(n: int)
  requires n >= 1
  ensures vasya_eats_with_strategy(n, n) * 2 >= n
  decreases n
{
  var cur := n;
  var remaining_after_vasya := 0;
  var remaining_after_petya := 0;
  if remaining_after_petya > 0 {
    VasyaEatsAtLeastHalfAtN(remaining_after_petya);
  }
}

lemma VasyaEatsIncreasing(n: int, k: int)
  requires n >= 1
  requires k >= 1
  ensures k < n ==> vasya_eats_with_strategy(n, k) < vasya_eats_with_strategy(n, k + 1)
  decreases n
{
  if k < n {
    var cur_k := k;
    var remaining_after_vasya_k := n - cur_k;
    var remaining_after_petya_k := remaining_after_vasya_k - remaining_after_vasya_k / 10;
    var cur_k1 := k + 1;
    var remaining_after_vasya_k1 := n - cur_k1;
    var remaining_after_petya_k1 := remaining_after_vasya_k1 - remaining_after_vasya_k1 / 10;
    if remaining_after_petya_k > 0 {
      VasyaEatsMonotonic(remaining_after_petya_k, k, k + 1);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures 1 <= result <= n
    ensures IsMinimalSolution(n, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed initialization and loop logic */
  result := n;
  VasyaEatsAtLeastHalfAtN(n);
  while result > 1
    invariant 1 <= result <= n
    invariant vasya_eats_with_strategy(n, result) * 2 >= n
    decreases result
  {
    if vasya_eats_with_strategy(n, result - 1) * 2 >= n {
      VasyaEatsMonotonic(n, result - 1, result);
      result := result - 1;
    } else {
      break;
    }
  }
}
// </vc-code>
