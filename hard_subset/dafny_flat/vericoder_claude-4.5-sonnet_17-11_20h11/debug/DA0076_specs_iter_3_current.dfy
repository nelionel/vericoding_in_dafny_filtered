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
/* helper modified by LLM (iteration 3): fixed sum lemma and added difference sum lemma */
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
      s[0] + sum(s[1..][..i]) + s[1..][i];
      { assert s[1..][..i] == s[1..i]; }
      { assert s[1..][i] == s[i]; }
      s[0] + sum(s[1..i]) + s[i];
      { assert s[..i] == [s[0]] + s[1..i]; }
      { assert sum(s[..i]) == s[0] + sum(s[1..i]); }
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

lemma sumDifference(s1: seq<int>, s2: seq<int>)
  requires |s1| == |s2|
  ensures sum(s1) - sum(s2) == sum(seq(|s1|, i requires 0 <= i < |s1| => s1[i] - s2[i]))
{
  if |s1| == 0 {
  } else {
    calc {
      sum(s1) - sum(s2);
      (s1[0] + sum(s1[1..])) - (s2[0] + sum(s2[1..]));
      (s1[0] - s2[0]) + (sum(s1[1..]) - sum(s2[1..]));
      { sumDifference(s1[1..], s2[1..]); }
      (s1[0] - s2[0]) + sum(seq(|s1[1..]|, i requires 0 <= i < |s1[1..]| => s1[1..][i] - s2[1..][i]));
      { assert seq(|s1|, i requires 0 <= i < |s1| => s1[i] - s2[i]) == [s1[0] - s2[0]] + seq(|s1[1..]|, i requires 0 <= i < |s1[1..]| => s1[1..][i] - s2[1..][i]); }
      sum(seq(|s1|, i requires 0 <= i < |s1| => s1[i] - s2[i]));
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
  /* code modified by LLM (iteration 3): proper calculation of additionalWalks with sumDifference lemma */
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
  
  sumDifference(finalSchedule, a);
  sumNonNegative(seq(n, j requires 0 <= j < n => finalSchedule[j] - a[j]));
  
  additionalWalks := sum(finalSchedule) - sum(a);
}
// </vc-code>
