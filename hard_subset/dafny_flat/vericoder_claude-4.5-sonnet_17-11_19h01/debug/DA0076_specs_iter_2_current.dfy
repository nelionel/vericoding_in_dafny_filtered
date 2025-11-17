// <vc-preamble>
function sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidInput(n: int, k: int, a: seq<int>)
{
    n >= 1 && |a| == n && k >= 0 && forall i :: 0 <= i < n ==> a[i] >= 0
}

predicate ValidOutput(a: seq<int>, finalSchedule: seq<int>, additionalWalks: int, k: int)
{
    |finalSchedule| == |a| &&
    additionalWalks >= 0 &&
    forall i :: 0 <= i < |a| ==> finalSchedule[i] >= a[i] &&
    forall i :: 0 <= i < |a| - 1 ==> finalSchedule[i] + finalSchedule[i + 1] >= k &&
    additionalWalks == sum(finalSchedule) - sum(a)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemmas to prove sum properties for slices */
function max(a: int, b: int): int { if a > b then a else b }

lemma sumDistributive(s1: seq<int>, s2: seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    calc {
      sum(s1 + s2);
      (s1 + s2)[0] + sum((s1 + s2)[1..]);
      s1[0] + sum((s1 + s2)[1..]);
      { assert (s1 + s2)[1..] == s1[1..] + s2; }
      s1[0] + sum(s1[1..] + s2);
      { sumDistributive(s1[1..], s2); }
      s1[0] + sum(s1[1..]) + sum(s2);
      sum(s1) + sum(s2);
    }
  }
}

lemma sumNonNegative(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures sum(s) >= 0
{
  if |s| == 0 {
  } else {
    sumNonNegative(s[1..]);
  }
}

lemma sumSliceExtend(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures sum(s[..i+1]) == sum(s[..i]) + s[i]
{
  if i == 0 {
    assert s[..1] == [s[0]];
  } else {
    calc {
      sum(s[..i+1]);
      { assert s[..i+1] == s[..i] + [s[i]]; }
      sum(s[..i] + [s[i]]);
      { sumDistributive(s[..i], [s[i]]); }
      sum(s[..i]) + sum([s[i]]);
      sum(s[..i]) + s[i];
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (additionalWalks: int, finalSchedule: seq<int>)
    requires ValidInput(n, k, a)
    ensures ValidOutput(a, finalSchedule, additionalWalks, k)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed loop invariants and added assertions */
{
  finalSchedule := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |finalSchedule| == i
    invariant forall j :: 0 <= j < i ==> finalSchedule[j] >= a[j]
    invariant forall j :: 0 <= j < i - 1 ==> finalSchedule[j] + finalSchedule[j + 1] >= k
  {
    var newVal: int;
    if i == 0 {
      if n == 1 {
        newVal := a[0];
      } else {
        newVal := max(a[0], k - a[1]);
      }
    } else {
      newVal := max(a[i], k - finalSchedule[i - 1]);
    }
    finalSchedule := finalSchedule + [newVal];
    i := i + 1;
  }
  
  additionalWalks := 0;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant additionalWalks == sum(finalSchedule[..i]) - sum(a[..i])
  {
    sumSliceExtend(finalSchedule, i);
    sumSliceExtend(a, i);
    additionalWalks := additionalWalks + (finalSchedule[i] - a[i]);
    i := i + 1;
  }
  
  assert finalSchedule[..n] == finalSchedule;
  assert a[..n] == a;
  assert additionalWalks == sum(finalSchedule) - sum(a);
  
  assert forall j :: 0 <= j < |a| ==> finalSchedule[j] - a[j] >= 0;
  sumNonNegative(seq(|a|, j requires 0 <= j < |a| => finalSchedule[j] - a[j]));
}
// </vc-code>
