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
lemma CapacityMonotonic(n1: int, n2: int, k: int, b: int, v: int)
    requires n1 >= 0 && n2 >= n1
    ensures BoxCapacity(n1, k, b, v) <= BoxCapacity(n2, k, b, v)
{
    var diff := n2 - n1;
    assert BoxCapacity(n2, k, b, v) == v * (n2 + min(b, (k - 1) * n2));
    assert BoxCapacity(n1, k, b, v) == v * (n1 + min(b, (k - 1) * n1));
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
{
    BoundedSearch(k, a, b, v);
    result := 1;
    while result < 1009
        invariant 1 <= result <= 1009
        invariant forall j :: 1 <= j < result ==> !CanStoreNuts(j, k, a, b, v)
        invariant exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v)
        decreases 1009 - result
    {
        if CanStoreNuts(result, k, a, b, v) {
            assert forall j :: 1 <= j < result ==> !CanStoreNuts(j, k, a, b, v);
            assert IsMinimalSolution(result, k, a, b, v);
            return;
        }
        result := result + 1;
    }
    assert result == 1009;
    assert forall j :: 1 <= j < 1009 ==> !CanStoreNuts(j, k, a, b, v);
    assert CanStoreNuts(1009, k, a, b, v);
    assert IsMinimalSolution(1009, k, a, b, v);
}
// </vc-code>
