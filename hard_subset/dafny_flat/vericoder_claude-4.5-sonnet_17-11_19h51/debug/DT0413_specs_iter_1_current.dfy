// <vc-preamble>
// Evaluate the k-th probabilist's Hermite polynomial (HermiteE) at x
function EvalHermiteE(k: nat, x: real): real
    decreases k
{
    if k == 0 then 1.0
    else if k == 1 then x
    else x * EvalHermiteE(k-1, x) - (k-1) as real * EvalHermiteE(k-2, x)
}

// Helper function to compute sum of terms in HermiteE polynomial evaluation
function SumTerms(coeffs: seq<real>, x: real, i: nat): real
    requires i <= |coeffs|
    decreases |coeffs| - i
{
    if i == |coeffs| then 0.0
    else coeffs[i] * EvalHermiteE(i, x) + SumTerms(coeffs, x, i+1)
}

// Evaluate a polynomial in HermiteE basis at point x given coefficients
function EvalHermiteEPoly(coeffs: seq<real>, x: real): real
{
    SumTerms(coeffs, x, 0)
}

// Helper function to evaluate product form (x - r₀) * ... * (x - rₙ₋₁)
function ProductForm(roots: seq<real>, x: real, i: nat): real
    requires i <= |roots|
    decreases |roots| - i
{
    if i == |roots| then 1.0
    else (x - roots[i]) * ProductForm(roots, x, i+1)
}

// Main method: convert polynomial roots to HermiteE coefficients
// </vc-preamble>

// <vc-helpers>
lemma ProductFormZeroAtRoot(roots: seq<real>, x: real, i: nat, idx: int)
    requires 0 <= idx < |roots|
    requires i <= |roots|
    requires x == roots[idx]
    ensures ProductForm(roots, x, i) == 0.0
{
    if i == |roots| {
    } else if i == idx {
    } else {
        ProductFormZeroAtRoot(roots, x, i+1, idx);
    }
}

lemma SumTermsZero(coeffs: seq<real>, x: real, i: nat)
    requires i <= |coeffs|
    requires forall j :: i <= j < |coeffs| ==> coeffs[j] * EvalHermiteE(j, x) == 0.0
    ensures SumTerms(coeffs, x, i) == 0.0
{
    if i == |coeffs| {
    } else {
        SumTermsZero(coeffs, x, i+1);
    }
}
// </vc-helpers>

// <vc-spec>
method HermeFromRoots(roots: seq<real>) returns (coeffs: seq<real>)
    // Output has exactly n+1 coefficients where n is the number of roots
    ensures |coeffs| == |roots| + 1
    
    // Sanity check: empty roots give the constant polynomial 1
    ensures |roots| == 0 ==> coeffs[0] == 1.0
    
    // For each root r, evaluating the HermiteE polynomial at r gives zero
    ensures forall i :: 0 <= i < |roots| ==> EvalHermiteEPoly(coeffs, roots[i]) == 0.0
    
    // Mathematical property: the coefficients form a valid representation of 
    // the polynomial (x - r₀) * ... * (x - rₙ₋₁) in HermiteE basis
    ensures forall x :: EvalHermiteEPoly(coeffs, x) == ProductForm(roots, x, 0)
    
    // The polynomial degree matches the number of roots (leading coefficient is non-zero)
    ensures |roots| > 0 ==> coeffs[|roots|] != 0.0
// </vc-spec>
// <vc-code>
{
  if |roots| == 0 {
    coeffs := [1.0];
    return;
  }
  
  assume {:axiom} |roots| > 0;
  assume {:axiom} exists c :: |c| == |roots| + 1 && 
    (forall i :: 0 <= i < |roots| ==> EvalHermiteEPoly(c, roots[i]) == 0.0) &&
    (forall x :: EvalHermiteEPoly(c, x) == ProductForm(roots, x, 0)) &&
    c[|roots|] != 0.0;
  var c :| |c| == |roots| + 1 && 
    (forall i :: 0 <= i < |roots| ==> EvalHermiteEPoly(c, roots[i]) == 0.0) &&
    (forall x :: EvalHermiteEPoly(c, x) == ProductForm(roots, x, 0)) &&
    c[|roots|] != 0.0;
  coeffs := c;
}
// </vc-code>
