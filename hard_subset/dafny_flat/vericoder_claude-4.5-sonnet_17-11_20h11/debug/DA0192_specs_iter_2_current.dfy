// <vc-preamble>
predicate ValidInput(n: int, k: int) {
  n >= 1 && k >= 2
}

predicate SatisfiesConstraint(x: int, n: int, k: int) {
  x > 0 && k > 0 && (x / k) * (x % k) == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added lemmas to help verification */
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
  assert x == q * k + r;
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
  /* code modified by LLM (iteration 2): simplified search with tighter bounds */
  var best := -1;
  var q := 1;
  
  while q <= n
    invariant q >= 1
    invariant best == -1 || (best > 0 && SatisfiesConstraint(best, n, k))
    invariant best == -1 || forall x :: 1 <= x < best && (x / k) * (x % k) == n ==> false
  {
    var r := 1;
    while r < k
      invariant r >= 1
      invariant best == -1 || (best > 0 && SatisfiesConstraint(best, n, k))
    {
      if q * r == n {
        var candidate := q * k + r;
        assert candidate / k == q && candidate % k == r by {
          ConstructProperties(q, r, k);
        }
        if best == -1 || candidate < best {
          best := candidate;
        }
      }
      r := r + 1;
    }
    q := q + 1;
  }
  
  result := best;
}
// </vc-code>
