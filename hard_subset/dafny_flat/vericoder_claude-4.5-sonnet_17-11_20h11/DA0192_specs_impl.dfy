// <vc-preamble>
predicate ValidInput(n: int, k: int) {
  n >= 1 && k >= 2
}

predicate SatisfiesConstraint(x: int, n: int, k: int) {
  x > 0 && k > 0 && (x / k) * (x % k) == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed ConstructProperties lemma proof */
lemma DivModBasic(x: int, k: int)
  requires k > 0
  ensures x == (x / k) * k + (x % k)
{
}

lemma DivModBounds(x: int, k: int)
  requires k > 0
  ensures 0 <= x % k < k
{
}

function ConstructFromDivMod(q: int, r: int, k: int): int
  requires k > 0
  requires 0 <= r < k
{
  q * k + r
}

lemma ConstructProperties(q: int, r: int, k: int)
  requires k > 0
  requires 0 <= r < k
  ensures var x := ConstructFromDivMod(q, r, k); x / k == q && x % k == r
{
  var x := q * k + r;
  calc {
    x / k;
  ==  { assert x == q * k + r; }
    (q * k + r) / k;
  ==  { assert 0 <= r < k; }
    q;
  }
  calc {
    x % k;
  ==  { assert x == q * k + r; }
    (q * k + r) % k;
  ==  { assert 0 <= r < k; }
    r;
  }
}

lemma AllSolutionsFound(n: int, k: int, bound: int, best: int)
  requires k >= 2
  requires n >= 1
  requires bound >= 1
  requires best > 0
  requires SatisfiesConstraint(best, n, k)
  requires forall q, r :: 1 <= q < bound && 1 <= r < k && q * r == n ==> q * k + r >= best
  ensures forall x :: 1 <= x < bound * k && (x / k) * (x % k) == n ==> x >= best
{
  forall x | 1 <= x < bound * k && (x / k) * (x % k) == n
    ensures x >= best
  {
    var q := x / k;
    var r := x % k;
    assert x == q * k + r;
    assert 0 <= r < k;
    assert q * r == n;
    if r >= 1 {
      assert 1 <= q < bound;
      assert x >= best;
    } else {
      assert r == 0;
      assert q * r == 0;
      assert false;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
  requires ValidInput(n, k)
  ensures result > 0
  ensures SatisfiesConstraint(result, n, k)
  ensures forall x :: x > 0 && (x / k) * (x % k) == n ==> result <= x
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed result initialization and loop invariants */
  var best := -1;
  var q := 1;
  
  while q <= n
    invariant q >= 1
    invariant best == -1 || (best > 0 && SatisfiesConstraint(best, n, k))
    invariant best == -1 || forall q2, r2 :: 1 <= q2 < q && 1 <= r2 < k && q2 * r2 == n ==> q2 * k + r2 >= best
  {
    var r := 1;
    while r < k
      invariant r >= 1
      invariant best == -1 || (best > 0 && SatisfiesConstraint(best, n, k))
      invariant best == -1 || forall q2, r2 :: 1 <= q2 < q && 1 <= r2 < k && q2 * r2 == n ==> q2 * k + r2 >= best
      invariant forall r2 :: 1 <= r2 < r && q * r2 == n ==> q * k + r2 >= best
    {
      if q * r == n {
        var candidate := q * k + r;
        ConstructProperties(q, r, k);
        assert candidate / k == q && candidate % k == r;
        assert SatisfiesConstraint(candidate, n, k);
        if best == -1 || candidate < best {
          best := candidate;
        }
      }
      r := r + 1;
    }
    q := q + 1;
  }
  
  if best == -1 {
    var candidate := n * k + 1;
    ConstructProperties(n, 1, k);
    assert candidate / k == n && candidate % k == 1;
    assert n * 1 == n;
    best := candidate;
  }
  
  result := best;
}
// </vc-code>
