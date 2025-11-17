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

function sumUpTo(s: seq<int>, i: int): int
  requires 0 <= i <= |s|
{
  if i == 0 then 0 else s[i - 1] + sumUpTo(s, i - 1)
}

lemma sumUpToComplete(s: seq<int>)
  ensures sumUpTo(s, |s|) == sum(s)
{
  if |s| == 0 {
  } else {
    calc {
      sumUpTo(s, |s|);
      s[|s| - 1] + sumUpTo(s, |s| - 1);
      {
        sumUpToComplete(s[..|s| - 1]);
        assert s[..|s| - 1] == s[..][..|s| - 1];
        assert s == s[..][..|s|];
      }
      s[|s| - 1] + sum(s[..|s| - 1]);
      {
        assert s[0] == s[..][0];
        assert s[1..] == s[..][1..];
      }
      sum(s);
    }
  }
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
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (additionalWalks: int, finalSchedule: seq<int>)
    requires ValidInput(n, k, a)
    ensures ValidOutput(a, finalSchedule, additionalWalks, k)
// </vc-spec>
// <vc-code>
{
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
    additionalWalks := additionalWalks + (finalSchedule[i] - a[i]);
    i := i + 1;
  }
  
  assert finalSchedule[..n] == finalSchedule;
  assert a[..n] == a;
}
// </vc-code>
