// <vc-preamble>
predicate ValidInput(n: int, sticks: seq<int>)
{
    1 <= n <= 1000 &&
    |sticks| == n &&
    (forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100)
}

function CostForT(sticks: seq<int>, t: int): int
    requires forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100
    requires 1 <= t <= 99
    ensures CostForT(sticks, t) >= 0
{
    SumCosts(sticks, t, 0)
}

function SumCosts(sticks: seq<int>, t: int, index: int): int
    requires forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100
    requires 1 <= t <= 99
    requires 0 <= index <= |sticks|
    ensures SumCosts(sticks, t, index) >= 0
    decreases |sticks| - index
{
    if index == |sticks| then 0
    else Max(0, Abs(t - sticks[index]) - 1) + SumCosts(sticks, t, index + 1)
}

function Abs(x: int): int
    ensures Abs(x) >= 0
{
    if x >= 0 then x else -x
}

function Max(a: int, b: int): int
    ensures Max(a, b) >= a && Max(a, b) >= b
{
    if a >= b then a else b
}

predicate IsOptimalT(sticks: seq<int>, t: int)
    requires forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100
    requires 1 <= t <= 99
{
    forall other_t :: 1 <= other_t <= 99 ==> 
        CostForT(sticks, t) <= CostForT(sticks, other_t)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): strengthened lemma to prove optimality directly */
lemma FindMinimumByIteration(sticks: seq<int>, current_t: int, current_min_cost: int, best_t: int)
    requires forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100
    requires 1 <= current_t <= 100
    requires 1 <= best_t <= 99
    requires current_min_cost == CostForT(sticks, best_t)
    requires forall t :: 1 <= t < current_t ==> current_min_cost <= CostForT(sticks, t)
    ensures current_t > 99 ==> IsOptimalT(sticks, best_t)
{
    if current_t > 99 {
        forall other_t | 1 <= other_t <= 99
            ensures CostForT(sticks, best_t) <= CostForT(sticks, other_t)
        {
            assert 1 <= other_t < current_t;
            assert current_min_cost <= CostForT(sticks, other_t);
            assert current_min_cost == CostForT(sticks, best_t);
        }
        assert forall other_t :: 1 <= other_t <= 99 ==> CostForT(sticks, best_t) <= CostForT(sticks, other_t);
    }
}
// </vc-helpers>

// <vc-spec>
method FindOptimalT(n: int, sticks: seq<int>) returns (t: int, min_cost: int)
    requires ValidInput(n, sticks)
    ensures 1 <= t <= 99
    ensures min_cost >= 0
    ensures min_cost == CostForT(sticks, t)
    ensures IsOptimalT(sticks, t)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added explicit assertion for IsOptimalT */
{
  t := 1;
  min_cost := CostForT(sticks, 1);
  var current_t := 2;
  
  while current_t <= 99
    invariant 2 <= current_t <= 100
    invariant 1 <= t <= 99
    invariant min_cost >= 0
    invariant min_cost == CostForT(sticks, t)
    invariant forall other_t :: 1 <= other_t < current_t ==> min_cost <= CostForT(sticks, other_t)
  {
    var cost := CostForT(sticks, current_t);
    if cost < min_cost {
      t := current_t;
      min_cost := cost;
    }
    current_t := current_t + 1;
  }
  
  FindMinimumByIteration(sticks, current_t, min_cost, t);
  assert IsOptimalT(sticks, t);
}
// </vc-code>
