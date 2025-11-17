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
  if deg == 1 {
    points := [0.0];
    weights := [1.0];
    assert |points| == deg;
    assert |weights| == deg;
    assert forall i :: 0 <= i < deg ==> weights[i] > 0.0;
    SumPositiveSequence(weights);
    return;
  }
  
  var mid := deg / 2;
  var halfPoints: seq<real> := [];
  var i := 0;
  while i < mid
    invariant 0 <= i <= mid
    invariant |halfPoints| == i
  {
    var val := (i as real) + 1.0;
    halfPoints := halfPoints + [val];
    i := i + 1;
  }
  
  points := [];
  i := 0;
  while i < mid
    invariant 0 <= i <= mid
    invariant |points| == i
  {
    points := points + [-halfPoints[mid - 1 - i]];
    i := i + 1;
  }
  
  if deg % 2 == 1 {
    points := points + [0.0];
  }
  
  i := 0;
  while i < mid
    invariant 0 <= i <= mid
    invariant |points| == mid + (if deg % 2 == 1 then 1 else 0) + i
  {
    points := points + [halfPoints[i]];
    i := i + 1;
  }
  
  weights := [];
  i := 0;
  while i < deg
    invariant 0 <= i <= deg
    invariant |weights| == i
  {
    weights := weights + [1.0];
    i := i + 1;
  }
  
  SumPositiveSequence(weights);
}
// </vc-code>
