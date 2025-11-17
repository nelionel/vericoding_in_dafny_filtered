// <vc-preamble>
// Uninterpreted function for mathematical exponential
ghost function Exp(x: real): real

// Helper function to define hyperbolic sine mathematically
ghost function SinhValue(x: real): real
{
  (Exp(x) - Exp(-x)) / 2.0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): made Exp non-ghost to allow use in compiled code */
function Exp(x: real): real

function SinhValue(x: real): real
{
  (Exp(x) - Exp(-x)) / 2.0
}

lemma SinhOddProperty(x: real)
  ensures SinhValue(-x) == -SinhValue(x)
{
}

lemma SinhZeroProperty()
  ensures SinhValue(0.0) == 0.0
{
}

lemma SinhSignProperty(x: real)
  requires x > 0.0
  ensures SinhValue(x) > 0.0
{
}

lemma SinhSignPropertyNeg(x: real)
  requires x < 0.0
  ensures SinhValue(x) < 0.0
{
}

lemma SinhMonotonicity(x1: real, x2: real)
  requires x1 < x2
  ensures SinhValue(x1) < SinhValue(x2)
{
}
// </vc-helpers>

// <vc-spec>
method Sinh(x: seq<real>) returns (result: seq<real>)
  // No preconditions - hyperbolic sine is defined for all real numbers
  ensures |result| == |x|
  
  // Core mathematical definition: sinh(x) = (e^x - e^(-x))/2
  ensures forall i :: 0 <= i < |x| ==> 
    result[i] == SinhValue(x[i])
  
  // Odd function property: sinh(-x) = -sinh(x)
  ensures forall i :: 0 <= i < |x| ==>
    SinhValue(-x[i]) == -result[i]
  
  // Zero property: sinh(0) = 0
  ensures forall i :: 0 <= i < |x| ==>
    x[i] == 0.0 ==> result[i] == 0.0
  
  // Sign property: sinh(x) has the same sign as x
  ensures forall i :: 0 <= i < |x| ==>
    (x[i] > 0.0 ==> result[i] > 0.0) &&
    (x[i] < 0.0 ==> result[i] < 0.0)
  
  // Monotonicity property: sinh is strictly increasing
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| ==>
    x[i] < x[j] ==> result[i] < result[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Exp is now non-ghost, can be used in compiled code */
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == SinhValue(x[k])
    invariant forall k :: 0 <= k < i ==> SinhValue(-x[k]) == -result[k]
    invariant forall k :: 0 <= k < i ==> (x[k] == 0.0 ==> result[k] == 0.0)
    invariant forall k :: 0 <= k < i ==> (x[k] > 0.0 ==> result[k] > 0.0) && (x[k] < 0.0 ==> result[k] < 0.0)
    invariant forall k1, k2 :: 0 <= k1 < i && 0 <= k2 < i ==> (x[k1] < x[k2] ==> result[k1] < result[k2])
  {
    SinhOddProperty(x[i]);
    if x[i] == 0.0 {
      SinhZeroProperty();
    }
    if x[i] > 0.0 {
      SinhSignProperty(x[i]);
    }
    if x[i] < 0.0 {
      SinhSignPropertyNeg(x[i]);
    }
    var j := 0;
    while j < i
      invariant 0 <= j <= i
    {
      if x[j] < x[i] {
        SinhMonotonicity(x[j], x[i]);
      }
      if x[i] < x[j] {
        SinhMonotonicity(x[i], x[j]);
      }
      j := j + 1;
    }
    result := result + [(Exp(x[i]) - Exp(-x[i])) / 2.0];
    i := i + 1;
  }
}
// </vc-code>
