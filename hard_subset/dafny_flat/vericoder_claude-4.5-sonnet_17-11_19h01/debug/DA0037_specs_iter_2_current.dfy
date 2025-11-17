// <vc-preamble>
predicate ValidInput(n: int, k: int, a: seq<int>)
{
    n >= 1 && k >= 1 && |a| == n &&
    (forall i :: 0 <= i < |a| ==> a[i] >= 1) &&
    (exists i :: 0 <= i < |a| && k % a[i] == 0)
}

predicate ValidBucket(k: int, bucketSize: int)
{
    bucketSize >= 1 && k % bucketSize == 0
}

function HoursNeeded(k: int, bucketSize: int): int
    requires ValidBucket(k, bucketSize)
{
    k / bucketSize
}

predicate IsOptimalChoice(k: int, a: seq<int>, chosenBucket: int)
{
    0 <= chosenBucket < |a| &&
    ValidBucket(k, a[chosenBucket]) &&
    (forall i :: 0 <= i < |a| && ValidBucket(k, a[i]) ==> a[i] <= a[chosenBucket])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed base case to handle exists requirement */
function FindMaxDivisor(k: int, a: seq<int>, upTo: int): int
  requires |a| >= 1
  requires 0 <= upTo <= |a|
  requires forall i :: 0 <= i < |a| ==> a[i] >= 1
  requires exists i :: 0 <= i < upTo && k % a[i] == 0
  ensures 0 <= FindMaxDivisor(k, a, upTo) < upTo
  ensures k % a[FindMaxDivisor(k, a, upTo)] == 0
  ensures forall i :: 0 <= i < upTo && k % a[i] == 0 ==> a[i] <= a[FindMaxDivisor(k, a, upTo)]
{
  if upTo == 1 then 0
  else if k % a[upTo - 1] == 0 then
    if exists i :: 0 <= i < upTo - 1 && k % a[i] == 0 then
      var prev := FindMaxDivisor(k, a, upTo - 1);
      if a[upTo - 1] > a[prev] then upTo - 1 else prev
    else
      upTo - 1
  else
    FindMaxDivisor(k, a, upTo - 1)
}

lemma FindMaxDivisorIsOptimal(k: int, a: seq<int>, upTo: int)
  requires |a| >= 1
  requires 0 <= upTo <= |a|
  requires forall i :: 0 <= i < |a| ==> a[i] >= 1
  requires exists i :: 0 <= i < upTo && k % a[i] == 0
  ensures IsOptimalChoice(k, a[..upTo], FindMaxDivisor(k, a, upTo))
{
  var idx := FindMaxDivisor(k, a, upTo);
  assert ValidBucket(k, a[idx]);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, k, a)
    ensures result >= 1
    ensures exists i :: IsOptimalChoice(k, a, i) && result == HoursNeeded(k, a[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): no changes needed */
{
  var maxIdx := FindMaxDivisor(k, a, n);
  result := HoursNeeded(k, a[maxIdx]);
  assert IsOptimalChoice(k, a, maxIdx);
}
// </vc-code>
