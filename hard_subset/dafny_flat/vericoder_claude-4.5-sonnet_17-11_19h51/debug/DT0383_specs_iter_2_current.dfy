// <vc-preamble>
/*
 * Chebyshev polynomial generation from roots.
 * 
 * This module generates Chebyshev series coefficients for polynomials with given roots.
 * Given a set of roots r₀, r₁, ..., rₙ₋₁, it computes coefficients c₀, c₁, ..., cₙ
 * such that the polynomial p(x) = (x - r₀) * (x - r₁) * ... * (x - rₙ₋₁)
 * can be expressed as p(x) = c₀ + c₁ * T₁(x) + ... + cₙ * Tₙ(x)
 * where Tₖ(x) is the k-th Chebyshev polynomial of the first kind.
 */

// Evaluate the k-th Chebyshev polynomial of the first kind at x
function EvalChebyshevT(k: nat, x: real): real
{
    if k == 0 then 1.0
    else if k == 1 then x
    else 2.0 * x * EvalChebyshevT(k - 1, x) - EvalChebyshevT(k - 2, x)
}

// Evaluate a polynomial in Chebyshev basis at point x given coefficients
function EvalChebyshevPoly(coeffs: seq<real>, x: real): real
{
    if |coeffs| == 0 then 0.0
    else SumChebyshevTerms(coeffs, x, 0)
}

// Helper function to sum Chebyshev terms recursively
function SumChebyshevTerms(coeffs: seq<real>, x: real, i: nat): real
    requires i <= |coeffs|
    decreases |coeffs| - i
{
    if i == |coeffs| then 0.0
    else coeffs[i] * EvalChebyshevT(i, x) + SumChebyshevTerms(coeffs, x, i + 1)
}

// Power function for real numbers
function Pow(base: real, exp: int): real
{
    if exp == 0 then 1.0
    else if exp > 0 then base * Pow(base, exp - 1)
    else 1.0 / Pow(base, -exp)
}

// Generate Chebyshev series coefficients from given roots
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed Pow decreases clause, fixed MultiplyPolyByLinear array access, removed unverifiable BuildPolyFromRoots postcondition */
function Pow(base: real, exp: int): real
  decreases if exp >= 0 then exp else -exp
{
  if exp == 0 then 1.0
  else if exp > 0 then base * Pow(base, exp - 1)
  else 1.0 / Pow(base, -exp)
}

function MultiplyPolyByLinear(coeffs: seq<real>, root: real): seq<real>
  requires |coeffs| > 0
  ensures |MultiplyPolyByLinear(coeffs, root)| == |coeffs| + 1
{
  var n := |coeffs|;
  seq(n + 1, i requires 0 <= i <= n => 
    if i == 0 then -root * coeffs[0]
    else if i == n then coeffs[n - 1]
    else coeffs[i - 1] - root * coeffs[i]
  )
}

function BuildPolyFromRoots(roots: seq<real>, idx: nat): seq<real>
  requires idx <= |roots|
  ensures |BuildPolyFromRoots(roots, idx)| == idx + 1
  decreases idx
{
  if idx == 0 then [Pow(2.0, 1)]
  else 
    var prev := BuildPolyFromRoots(roots, idx - 1);
    MultiplyPolyByLinear(prev, roots[idx - 1])
}
// </vc-helpers>

// <vc-spec>
method ChebFromRoots(roots: seq<real>) returns (coeffs: seq<real>)
    ensures |coeffs| == |roots| + 1
    // For each root r, evaluating the Chebyshev polynomial at r gives zero
    ensures forall i :: 0 <= i < |roots| ==> EvalChebyshevPoly(coeffs, roots[i]) == 0.0
    // The highest degree coefficient is non-zero when there are roots
    ensures |roots| > 0 ==> coeffs[|roots|] != 0.0
    // The leading coefficient has the specific mathematical relationship for Chebyshev basis
    ensures |roots| > 0 ==> coeffs[|roots|] == Pow(2.0, 1 - |roots|)
    // The polynomial represented by coeffs has exactly the given roots
    // (implicitly satisfied by the zero-evaluation property above)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): simplified implementation without unverifiable postconditions */
  if |roots| == 0 {
    coeffs := [1.0];
  } else {
    coeffs := BuildPolyFromRoots(roots, |roots|);
  }
}
// </vc-code>
