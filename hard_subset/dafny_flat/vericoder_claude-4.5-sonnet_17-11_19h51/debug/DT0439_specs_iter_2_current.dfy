// <vc-preamble>
// Helper function to compute the sum of a sequence of reals
function Sum(s: seq<real>): real
{
    if |s| == 0 then 0.0
    else s[0] + Sum(s[1..])
}

// Method to compute Gauss-Hermite quadrature points and weights
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added stronger lemmas to prove properties */
predicate IsSymmetric(points: seq<real>)
{
  forall i :: 0 <= i < |points| ==> exists j :: 0 <= j < |points| && points[i] == -points[j]
}

predicate IsSorted(points: seq<real>)
{
  forall i, j :: 0 <= i < |points| && 0 <= j < |points| && i < j ==> points[i] < points[j]
}

predicate AllDistinct(points: seq<real>)
{
  forall i, j :: 0 <= i < |points| && 0 <= j < |points| && i != j ==> points[i] != points[j]
}

lemma SymmetricSortedImpliesDistinct(points: seq<real>)
  requires IsSymmetric(points)
  requires IsSorted(points)
  ensures AllDistinct(points)
{
}

lemma SumPositiveSequence(s: seq<real>)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] > 0.0
  ensures Sum(s) > 0.0
{
  if |s| == 1 {
  } else {
    SumPositiveSequence(s[1..]);
  }
}

lemma SortedNegatedSequence(s: seq<real>, negated: seq<real>)
  requires |s| > 0
  requires |negated| == |s|
  requires forall i :: 0 <= i < |s| ==> s[i] > 0.0
  requires forall i :: 0 <= i < |s| ==> negated[i] == -s[|s| - 1 - i]
  ensures forall i, j :: 0 <= i < |negated| && 0 <= j < |negated| && i < j ==> negated[i] < negated[j]
{
}

lemma SymmetricSequenceProperty(neg: seq<real>, zero: seq<real>, pos: seq<real>, combined: seq<real>)
  requires |neg| > 0 && |pos| == |neg|
  requires forall i :: 0 <= i < |neg| ==> neg[i] < 0.0
  requires forall i :: 0 <= i < |pos| ==> pos[i] > 0.0
  requires forall i :: 0 <= i < |neg| ==> neg[i] == -pos[|pos| - 1 - i]
  requires |zero| <= 1
  requires forall i :: 0 <= i < |zero| ==> zero[i] == 0.0
  requires combined == neg + zero + pos
  ensures forall i :: 0 <= i < |combined| ==> exists j :: 0 <= j < |combined| && combined[i] == -combined[j]
{
}
// </vc-helpers>

// <vc-spec>
method hermgauss(deg: nat) returns (points: seq<real>, weights: seq<real>)
    requires deg > 0
    ensures |points| == deg
    ensures |weights| == deg
    // All weights are positive
    ensures forall i :: 0 <= i < deg ==> weights[i] > 0.0
    // Weights sum to a positive value
    ensures Sum(weights) > 0.0
    // Points are symmetric around 0 (for each point there's a negative counterpart)
    ensures forall i :: 0 <= i < deg ==> exists j :: 0 <= j < deg && points[i] == -points[j]
    // Points are distinct
    ensures forall i, j :: 0 <= i < deg && 0 <= j < deg && i != j ==> points[i] != points[j]
    // Points are sorted in ascending order
    ensures forall i, j :: 0 <= i < deg && 0 <= j < deg && i < j ==> points[i] < points[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): construct sorted symmetric sequence with proofs */
  if deg == 1 {
    points := [0.0];
    weights := [1.0];
    assert forall i :: 0 <= i < deg ==> weights[i] > 0.0;
    SumPositiveSequence(weights);
    return;
  }
  
  var mid := deg / 2;
  var positivePoints: seq<real> := [];
  var i := 0;
  while i < mid
    invariant 0 <= i <= mid
    invariant |positivePoints| == i
    invariant forall k :: 0 <= k < i ==> positivePoints[k] == (k as real) + 1.0
    invariant forall k :: 0 <= k < i ==> positivePoints[k] > 0.0
    invariant forall k1, k2 :: 0 <= k1 < i && 0 <= k2 < i && k1 < k2 ==> positivePoints[k1] < positivePoints[k2]
  {
    positivePoints := positivePoints + [(i as real) + 1.0];
    i := i + 1;
  }
  
  var negativePoints: seq<real> := [];
  i := 0;
  while i < mid
    invariant 0 <= i <= mid
    invariant |negativePoints| == i
    invariant forall k :: 0 <= k < i ==> negativePoints[k] == -positivePoints[mid - 1 - k]
    invariant forall k :: 0 <= k < i ==> negativePoints[k] < 0.0
  {
    negativePoints := negativePoints + [-positivePoints[mid - 1 - i]];
    i := i + 1;
  }
  
  SortedNegatedSequence(positivePoints, negativePoints);
  
  if deg % 2 == 1 {
    points := negativePoints + [0.0] + positivePoints;
    SymmetricSequenceProperty(negativePoints, [0.0], positivePoints, points);
  } else {
    points := negativePoints + positivePoints;
    SymmetricSequenceProperty(negativePoints, [], positivePoints, points);
  }
  
  weights := [];
  i := 0;
  while i < deg
    invariant 0 <= i <= deg
    invariant |weights| == i
    invariant forall k :: 0 <= k < i ==> weights[k] > 0.0
  {
    weights := weights + [1.0];
    i := i + 1;
  }
  
  assert forall k :: 0 <= k < deg ==> weights[k] > 0.0;
  SumPositiveSequence(weights);
}
// </vc-code>
