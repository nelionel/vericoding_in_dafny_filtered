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
function max(a: int, b: int): int { if a > b then a else b }

function computeSchedule(a: seq<int>, k: int, i: int): seq<int>
  requires |a| > 0
  requires 0 <= i <= |a|
  decreases |a| - i
{
  if i == 0 then
    if |a| == 1 then a else [max(a[0], k - a[1])] + computeSchedule(a, k, 1)
  else if i == |a| then
    []
  else if i == |a| - 1 then
    [max(a[i], k - computeSchedule(a, k, i - 1)[i - 1])]
  else
    [max(a[i], k - computeSchedule(a, k, i - 1)[i - 1])] + computeSchedule(a, k, i + 1)
}

lemma sumDistributive(s1: seq<int>, s2: seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    calc {
      sum(s1 + s2);
      (s1 + s2)[0] + sum((s1 + s2)[1..]);
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
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (additionalWalks: int, finalSchedule: seq<int>)
    requires ValidInput(n, k, a)
    ensures ValidOutput(a, finalSchedule, additionalWalks, k)
// </vc-spec>
// <vc-code>
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
    additionalWalks := additionalWalks + (finalSchedule[i] - a[i]);
    i := i + 1;
  }
}
// </vc-code>
