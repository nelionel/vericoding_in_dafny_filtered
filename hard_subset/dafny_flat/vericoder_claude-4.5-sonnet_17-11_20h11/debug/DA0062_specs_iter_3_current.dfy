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
/* helper modified by LLM (iteration 3): fixed monotonicity lemma by ensuring both recursive calls are made with valid arguments */
lemma VasyaEatsMonotonic(n: int, k1: int, k2: int)
    requires n >= 1
    requires k1 >= 1 && k2 >= 1
    requires k1 <= k2
    ensures vasya_eats_with_strategy(n, k1) <= vasya_eats_with_strategy(n, k2)
    decreases n
{
    if n <= 0 {
    } else {
        var cur1 := if n < k1 then n else k1;
        var cur2 := if n < k2 then n else k2;
        var rem1 := n - cur1;
        var rem2 := n - cur2;
        var next1 := rem1 - rem1 / 10;
        var next2 := rem2 - rem2 / 10;
        if next1 > 0 && next2 > 0 {
            VasyaEatsMonotonic(next1, k1, k2);
            VasyaEatsMonotonic(next2, k1, k2);
            if next1 < next2 {
                VasyaEatsMonotonic(next1, k1, k2);
                VasyaEatsMonotonic(next2, k1, k2);
            }
        } else if next1 > 0 {
            VasyaEatsMonotonic(next1, k1, k2);
        } else if next2 > 0 {
            VasyaEatsMonotonic(next2, k1, k2);
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
/* code modified by LLM (iteration 3): ensure postcondition by explicitly invoking lemma before loop exit */
{
  result := n;
  while result > 1
    invariant 1 <= result <= n
    invariant vasya_eats_with_strategy(n, result) * 2 >= n
    decreases result
  {
    if result > 1 {
      VasyaEatsMonotonic(n, result - 1, result);
      if vasya_eats_with_strategy(n, result - 1) * 2 >= n {
        result := result - 1;
      } else {
        assert vasya_eats_with_strategy(n, result - 1) * 2 < n;
        assert vasya_eats_with_strategy(n, result) * 2 >= n;
        break;
      }
    }
  }
  assert vasya_eats_with_strategy(n, result) * 2 >= n;
  assert result == 1 || vasya_eats_with_strategy(n, result - 1) * 2 < n;
}
// </vc-code>
