// <vc-preamble>
function min(x: int, y: int): int
{
    if x <= y then x else y
}

predicate ValidInput(k: int, a: int, b: int, v: int)
{
    2 <= k <= 1000 && 1 <= a <= 1000 && 1 <= b <= 1000 && 1 <= v <= 1000
}

function BoxCapacity(numBoxes: int, k: int, b: int, v: int): int
    requires numBoxes >= 0
{
    v * (numBoxes + min(b, (k - 1) * numBoxes))
}

predicate CanStoreNuts(numBoxes: int, k: int, a: int, b: int, v: int)
    requires numBoxes >= 0
{
    a <= BoxCapacity(numBoxes, k, b, v)
}

predicate IsMinimalSolution(result: int, k: int, a: int, b: int, v: int)
    requires result >= 1
{
    CanStoreNuts(result, k, a, b, v) &&
    (result == 1 || !CanStoreNuts(result - 1, k, a, b, v))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added proof for min monotonicity */
lemma CapacityMonotonic(n1: int, n2: int, k: int, b: int, v: int)
    requires n1 >= 0 && n2 >= n1
    ensures BoxCapacity(n1, k, b, v) <= BoxCapacity(n2, k, b, v)
{
    var cap1 := v * (n1 + min(b, (k - 1) * n1));
    var cap2 := v * (n2 + min(b, (k - 1) * n2));
    assert cap1 == BoxCapacity(n1, k, b, v);
    assert cap2 == BoxCapacity(n2, k, b, v);
    
    if v > 0 {
        assert n2 >= n1;
        assert (k - 1) * n2 >= (k - 1) * n1;
        assert min(b, (k - 1) * n2) >= min(b, (k - 1) * n1);
        assert n2 + min(b, (k - 1) * n2) >= n1 + min(b, (k - 1) * n1);
        assert v * (n2 + min(b, (k - 1) * n2)) >= v * (n1 + min(b, (k - 1) * n1));
    } else if v < 0 {
        assert n2 >= n1;
        assert (k - 1) * n2 >= (k - 1) * n1;
        assert min(b, (k - 1) * n2) >= min(b, (k - 1) * n1);
        assert n2 + min(b, (k - 1) * n2) >= n1 + min(b, (k - 1) * n1);
        assert v * (n2 + min(b, (k - 1) * n2)) <= v * (n1 + min(b, (k - 1) * n1));
    } else {
        assert v == 0;
        assert cap1 == 0 && cap2 == 0;
    }
}

lemma CanStoreMonotonic(n1: int, n2: int, k: int, a: int, b: int, v: int)
    requires n1 >= 0 && n2 >= n1
    requires CanStoreNuts(n1, k, a, b, v)
    ensures CanStoreNuts(n2, k, a, b, v)
{
    CapacityMonotonic(n1, n2, k, b, v);
    assert a <= BoxCapacity(n1, k, b, v) <= BoxCapacity(n2, k, b, v);
}

lemma BoundedSearch(k: int, a: int, b: int, v: int)
    requires ValidInput(k, a, b, v)
    ensures exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v)
{
    var maxBoxes := 1009;
    assert BoxCapacity(maxBoxes, k, b, v) == v * (maxBoxes + min(b, (k - 1) * maxBoxes));
    assert min(b, (k - 1) * maxBoxes) >= 0;
    assert BoxCapacity(maxBoxes, k, b, v) >= v * maxBoxes >= 1 * 1009 >= a;
    assert CanStoreNuts(maxBoxes, k, a, b, v);
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, a: int, b: int, v: int) returns (result: int)
    requires ValidInput(k, a, b, v)
    ensures result >= 1
    ensures result <= 1009
    ensures IsMinimalSolution(result, k, a, b, v)
    ensures exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v) && result == i && 
            (forall j :: 1 <= j < i ==> !CanStoreNuts(j, k, a, b, v))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed loop condition to ensure all cases covered */
{
    BoundedSearch(k, a, b, v);
    result := 1;
    while result <= 1009
        invariant 1 <= result <= 1010
        invariant forall j :: 1 <= j < result ==> !CanStoreNuts(j, k, a, b, v)
        invariant exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v)
        decreases 1010 - result
    {
        if CanStoreNuts(result, k, a, b, v) {
            assert forall j :: 1 <= j < result ==> !CanStoreNuts(j, k, a, b, v);
            assert IsMinimalSolution(result, k, a, b, v);
            return;
        }
        result := result + 1;
    }
    assert false;
}
// </vc-code>
