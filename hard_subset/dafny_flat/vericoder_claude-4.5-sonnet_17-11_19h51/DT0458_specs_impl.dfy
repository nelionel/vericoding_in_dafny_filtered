// <vc-preamble>
// Helper function to evaluate a Laguerre polynomial at a given point
function EvaluateLaguerrePolynomial(coeffs: seq<real>, x: real): real
  requires |coeffs| > 0
{
  if |coeffs| == 1 then
    coeffs[0]
  else
    coeffs[0] + EvaluateLaguerrePolynomial(coeffs[1..], x) * LaguerrePolynomialValue(|coeffs| - 1, x)
}

// Helper function to compute the value of the nth Laguerre polynomial at x
function LaguerrePolynomialValue(n: nat, x: real): real
{
  if n == 0 then 1.0
  else if n == 1 then 1.0 - x
  else 
    ((2.0 * n as real - 1.0 - x) * LaguerrePolynomialValue(n - 1, x) - (n as real - 1.0) * LaguerrePolynomialValue(n - 2, x)) / n as real
}

// Helper function to evaluate a standard polynomial at a given point  
function EvaluatePolynomial(coeffs: seq<real>, x: real): real
  requires |coeffs| > 0
{
  if |coeffs| == 1 then
    coeffs[0]
  else
    coeffs[0] + x * EvaluatePolynomial(coeffs[1..], x)
}

// Convert a Laguerre series to a polynomial
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Implement complete conversion logic using basis expansion */
function LaguerreToPowerBasis(c: seq<real>, degree: nat): seq<real>
  requires |c| > 0
  requires degree == |c|
  ensures |LaguerreToPowerBasis(c, degree)| == degree
  decreases degree
{
  if degree == 1 then c
  else
    var smaller := LaguerreToPowerBasis(c[..|c|-1], degree - 1);
    AddLaguerreContribution(smaller, c[|c|-1], |c|-1)
}

function AddLaguerreContribution(poly: seq<real>, coeff: real, n: nat): seq<real>
  requires |poly| == n
  ensures |AddLaguerreContribution(poly, coeff, n)| == n + 1
{
  var lagPoly := GetLaguerrePolyCoeffs(n);
  AddPolynomials(ExtendPoly(poly), ScalePolynomial(lagPoly, coeff))
}

function GetLaguerrePolyCoeffs(n: nat): seq<real>
  ensures |GetLaguerrePolyCoeffs(n)| == n + 1
  decreases n
{
  if n == 0 then [1.0]
  else if n == 1 then [1.0, -1.0]
  else
    var L_n_minus_1 := GetLaguerrePolyCoeffs(n - 1);
    var L_n_minus_2 := GetLaguerrePolyCoeffs(n - 2);
    var term1 := ScalePolynomial(AddPolynomials(ScalePolynomial(L_n_minus_1, 2.0 * n as real - 1.0), ScaleAndShiftPolynomial(L_n_minus_1, -1.0)), 1.0 / n as real);
    var term2 := ScalePolynomial(ExtendPoly(L_n_minus_2), -(n as real - 1.0) / n as real);
    AddPolynomials(term1, term2)
}

function ExtendPoly(p: seq<real>): seq<real>
  ensures |ExtendPoly(p)| == |p| + 1
{
  p + [0.0]
}

function ScalePolynomial(p: seq<real>, scale: real): seq<real>
  ensures |ScalePolynomial(p, scale)| == |p|
{
  seq(|p|, i requires 0 <= i < |p| => p[i] * scale)
}

function ScaleAndShiftPolynomial(p: seq<real>, scale: real): seq<real>
  ensures |ScaleAndShiftPolynomial(p, scale)| == |p| + 1
{
  [0.0] + ScalePolynomial(p, scale)
}

function AddPolynomials(p1: seq<real>, p2: seq<real>): seq<real>
  requires |p1| == |p2|
  ensures |AddPolynomials(p1, p2)| == |p1|
{
  seq(|p1|, i requires 0 <= i < |p1| => p1[i] + p2[i])
}
// </vc-helpers>

// <vc-spec>
method Lag2Poly(c: seq<real>) returns (result: seq<real>)
  requires |c| > 0
  ensures |result| == |c|
  ensures forall x: real :: EvaluatePolynomial(result, x) == EvaluateLaguerrePolynomial(c, x)
  ensures |c| == 1 ==> result == c
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Use basis expansion approach */
  if |c| == 1 {
    result := c;
  } else {
    result := LaguerreToPowerBasis(c, |c|);
  }
}
// </vc-code>
