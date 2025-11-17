// <vc-preamble>
/*
 * Calculate exp(x) - 1 for all elements in the vector.
 * This function provides greater precision than exp(x) - 1 for small values of x.
 * Implements element-wise expm1 computation with enhanced numerical precision.
 */

// Mathematical function declarations for specification
function Exp(x: real): real
{
  1.0 + x // Placeholder implementation for compilation
}

function Abs(x: real): real
  ensures Abs(x) >= 0.0
  ensures x >= 0.0 ==> Abs(x) == x
  ensures x < 0.0 ==> Abs(x) == -x
{
  if x >= 0.0 then x else -x
}

// Main expm1 method that computes exp(x) - 1 element-wise with enhanced precision
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added lemmas to establish mathematical properties of Exp */
function Expm1Value(x: real): real
{
  Exp(x) - 1.0
}

lemma ExpProperties(x: real, y: real)
  ensures x < y ==> Exp(x) < Exp(y)
  ensures x == 0.0 ==> Exp(x) == 1.0
  ensures x > 0.0 ==> Exp(x) > 1.0 + x
  ensures x < 0.0 ==> 0.0 < Exp(x) < 1.0
  ensures Exp(x) > 0.0
{
}

lemma ExpMonotonicity(x: real, y: real)
  requires x < y
  ensures Exp(x) - 1.0 < Exp(y) - 1.0
{
  ExpProperties(x, y);
}

lemma ExpSmallValues(x: real)
  requires Abs(x) <= 0.1
  ensures Abs(Exp(x) - 1.0 - x) <= Abs(x) * Abs(x)
{
}

lemma ExpSignPreservation(x: real)
  requires Abs(x) <= 1.0
  ensures x > 0.0 ==> Exp(x) - 1.0 > 0.0
  ensures x < 0.0 ==> Exp(x) - 1.0 < 0.0
{
  ExpProperties(x, 0.0);
}
// </vc-helpers>

// <vc-spec>
method Expm1(x: seq<real>) returns (result: seq<real>)
  // Output vector has same length as input
  ensures |result| == |x|
  // For each element i in the vectors, all mathematical properties hold
  ensures forall i :: 0 <= i < |x| ==> (
    // Basic mathematical property: result equals exp(x) - 1
    result[i] == Exp(x[i]) - 1.0 &&
    // Monotonicity property: expm1 is strictly increasing across elements
    (forall j :: 0 <= j < |x| && x[i] < x[j] ==> result[i] < result[j]) &&
    // Identity property: expm1(0) = 0
    (x[i] == 0.0 ==> result[i] == 0.0) &&
    // Asymptotic behavior for small values: exp(x) - 1 ≈ x for small x
    (Abs(x[i]) <= 0.1 ==> Abs(result[i] - x[i]) <= Abs(x[i]) * Abs(x[i])) &&
    // Sign preservation for small values
    (Abs(x[i]) <= 1.0 ==> ((x[i] > 0.0 ==> result[i] > 0.0) && (x[i] < 0.0 ==> result[i] < 0.0))) &&
    // Lower bound for positive values: expm1(x) > x for x > 0
    (x[i] > 0.0 ==> result[i] > x[i]) &&
    // Upper bound for all values: expm1(x) > -1 for all x
    result[i] > -1.0
  )
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added lemma calls in loop to establish invariant */
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> (
      result[k] == Exp(x[k]) - 1.0 &&
      (forall j :: 0 <= j < |x| && x[k] < x[j] ==> result[k] < Exp(x[j]) - 1.0) &&
      (x[k] == 0.0 ==> result[k] == 0.0) &&
      (Abs(x[k]) <= 0.1 ==> Abs(result[k] - x[k]) <= Abs(x[k]) * Abs(x[k])) &&
      (Abs(x[k]) <= 1.0 ==> ((x[k] > 0.0 ==> result[k] > 0.0) && (x[k] < 0.0 ==> result[k] < 0.0))) &&
      (x[k] > 0.0 ==> result[k] > x[k]) &&
      result[k] > -1.0
    )
  {
    var val := Exp(x[i]) - 1.0;
    
    forall j | 0 <= j < |x| && x[i] < x[j]
      ensures val < Exp(x[j]) - 1.0
    {
      ExpMonotonicity(x[i], x[j]);
    }
    
    if Abs(x[i]) <= 0.1 {
      ExpSmallValues(x[i]);
    }
    
    if Abs(x[i]) <= 1.0 {
      ExpSignPreservation(x[i]);
    }
    
    if x[i] > 0.0 {
      ExpProperties(x[i], 0.0);
    }
    
    ExpProperties(x[i], x[i]);
    
    result := result + [val];
    i := i + 1;
  }
}
// </vc-code>
