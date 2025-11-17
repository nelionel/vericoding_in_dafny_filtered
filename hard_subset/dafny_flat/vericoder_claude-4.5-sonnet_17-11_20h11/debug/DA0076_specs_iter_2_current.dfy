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
/* helper modified by LLM (iteration 2): added lemmas for sum properties */
function max(a: int, b: int): int { if a > b then a else b }

lemma sumSingleElement(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures sum(s[..i+1]) == sum(s[..i]) + s[i]
{
  if i == 0 {
    calc {
      sum(s[..1]);
      sum([s[0]]);
      s[0] + sum([]);
      s[0] + 0;
      s[0];
      sum([]) + s[0];
      sum(s[..0]) + s[0];
    }
  } else {
    calc {
      sum(s[..i+1]);
      s[0] + sum(s[1..i+1]);
      { sumSingleElement(s[1..], i-1); }
      s[0] + sum(s[1..i]) + s[i];
      { assert s[1..i] == s[..i][1..]; }
      sum(s[..i]) + s[i];
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
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (additionalWalks: int, finalSchedule: seq<int>)
    requires ValidInput(n, k, a)
    ensures ValidOutput(a, finalSchedule, additionalWalks, k)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed additionalWalks calculation and loop invariants */
  finalSchedule := a;
  var i := 0;
  
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant |finalSchedule| == n
    invariant forall j :: 0 <= j < n ==> finalSchedule[j] >= a[j]
    invariant forall j :: 0 <= j < i ==> finalSchedule[j] + finalSchedule[j + 1] >= k
  {
    if finalSchedule[i] + finalSchedule[i + 1] < k {
      var needed := k - finalSchedule[i];
      finalSchedule := finalSchedule[i + 1 := needed];
    }
    i := i + 1;
  }
  
  additionalWalks := 0;
  i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant additionalWalks == sum(finalSchedule[..i]) - sum(a[..i])
  {
    sumSingleElement(finalSchedule, i);
    sumSingleElement(a, i);
    additionalWalks := additionalWalks + (finalSchedule[i] - a[i]);
    i := i + 1;
  }
  
  assert finalSchedule[..n] == finalSchedule;
  assert a[..n] == a;
  
  assert forall j :: 0 <= j < n ==> finalSchedule[j] >= a[j];
  assert forall j :: 0 <= j < n ==> finalSchedule[j] - a[j] >= 0;
  sumNonNegative(seq(n, j requires 0 <= j < n => finalSchedule[j] - a[j]));
}
// </vc-code>
