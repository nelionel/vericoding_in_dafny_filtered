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
/* helper modified by LLM (iteration 3): added lemma to prove capacity monotonicity */
lemma CapacityIncreases(i: int, k: int, b: int, v: int)
  requires i >= 0
  requires k >= 2 && b >= 1 && v >= 1
  ensures BoxCapacity(i + 1, k, b, v) >= BoxCapacity(i, k, b, v)
{
  var cap1 := BoxCapacity(i, k, b, v);
  var cap2 := BoxCapacity(i + 1, k, b, v);
  var m1 := min(b, (k - 1) * i);
  var m2 := min(b, (k - 1) * (i + 1));
  assert m2 >= m1;
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
/* code modified by LLM (iteration 3): added parentheses to fix indentation warning */
{
  result := 1;
  var capacity := v * (1 + min(b, (k - 1) * 1));
  
  while result < 1009 && capacity < a
    invariant 1 <= result <= 1009
    invariant capacity == BoxCapacity(result, k, b, v)
    invariant forall j :: 1 <= j < result ==> !CanStoreNuts(j, k, a, b, v)
    decreases 1009 - result
  {
    result := result + 1;
    capacity := v * (result + min(b, (k - 1) * result));
    CapacityIncreases(result - 1, k, b, v);
  }
  
  assert CanStoreNuts(result, k, a, b, v);
  assert result == 1 || !CanStoreNuts(result - 1, k, a, b, v);
  assert IsMinimalSolution(result, k, a, b, v);
  assert forall j :: 1 <= j < result ==> !CanStoreNuts(j, k, a, b, v);
  assert (exists i :: 1 <= i <= 1009 && CanStoreNuts(i, k, a, b, v) && result == i && (forall j :: 1 <= j < i ==> !CanStoreNuts(j, k, a, b, v)));
}
// </vc-code>
