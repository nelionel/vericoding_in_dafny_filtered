// <vc-preamble>
predicate ValidInput(n: int, k: int, M: int, D: int) {
    2 <= n && 2 <= k <= n && 1 <= M <= n && 1 <= D <= n && M * D * k >= n
}

function CandiesUsed(x: int, d: int, k: int): int {
    x * ((d - 1) * k + 1)
}

predicate ValidDistribution(x: int, d: int, n: int, k: int, M: int, D: int) {
    1 <= x <= M && 1 <= d <= D && CandiesUsed(x, d, k) <= n
}

function Person1Candies(x: int, d: int): int {
    x * d
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added requires for x1,d1 >= 1 and proof body */
lemma CandiesUsedMonotonic(x: int, d: int, k: int)
    requires x >= 1 && d >= 1 && k >= 2
    ensures CandiesUsed(x, d, k) >= x * d
{
    assert CandiesUsed(x, d, k) == x * ((d - 1) * k + 1);
    assert (d - 1) * k + 1 >= (d - 1) * 2 + 1;
    assert (d - 1) * 2 + 1 == 2 * d - 1 >= d;
}

/* helper modified by LLM (iteration 2): added requires for positivity */
lemma Person1CandiesMonotonic(x1: int, d1: int, x2: int, d2: int)
    requires x1 >= 1 && d1 >= 1 && x2 >= 1 && d2 >= 1
    requires x1 <= x2 && d1 <= d2
    ensures Person1Candies(x1, d1) <= Person1Candies(x2, d2)
{
    assert Person1Candies(x1, d1) == x1 * d1;
    assert Person1Candies(x2, d2) == x2 * d2;
    assert x1 * d1 <= x1 * d2;
    assert x1 * d2 <= x2 * d2;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, M: int, D: int) returns (result: int)
    requires ValidInput(n, k, M, D)
    ensures result >= 0
    ensures result <= M * D
    ensures forall x: int, d: int :: ValidDistribution(x, d, n, k, M, D) ==> Person1Candies(x, d) <= result
    ensures exists x: int, d: int :: ValidDistribution(x, d, n, k, M, D) && Person1Candies(x, d) == result
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed loop invariants and added witness tracking */
    result := 0;
    var x := 1;
    var witnessX := 1;
    var witnessD := 1;
    
    while x <= M
        invariant 1 <= x <= M + 1
        invariant result >= 0
        invariant result <= M * D
        invariant 1 <= witnessX <= M && 1 <= witnessD <= D
        invariant ValidDistribution(witnessX, witnessD, n, k, M, D)
        invariant Person1Candies(witnessX, witnessD) == result
        invariant forall x0: int, d0: int :: x0 < x && ValidDistribution(x0, d0, n, k, M, D) ==> Person1Candies(x0, d0) <= result
    {
        var d := 1;
        while d <= D
            invariant 1 <= d <= D + 1
            invariant 1 <= witnessX <= M && 1 <= witnessD <= D
            invariant ValidDistribution(witnessX, witnessD, n, k, M, D)
            invariant Person1Candies(witnessX, witnessD) == result
            invariant forall x0: int, d0: int :: x0 < x && ValidDistribution(x0, d0, n, k, M, D) ==> Person1Candies(x0, d0) <= result
            invariant forall d0: int :: d0 < d && ValidDistribution(x, d0, n, k, M, D) ==> Person1Candies(x, d0) <= result
        {
            if CandiesUsed(x, d, k) <= n {
                var candies := Person1Candies(x, d);
                if candies > result {
                    result := candies;
                    witnessX := x;
                    witnessD := d;
                }
            }
            d := d + 1;
        }
        x := x + 1;
    }
}
// </vc-code>
