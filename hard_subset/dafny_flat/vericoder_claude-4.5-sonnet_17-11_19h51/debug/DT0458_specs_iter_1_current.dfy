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
function ConvertLaguerreCoefficient(c: seq<real>, idx: nat, polyDegree: nat): real
  requires idx < |c|
  requires polyDegree < |c|
{
  c[idx] * LaguerrePolynomialCoefficient(idx, polyDegree)
}

function LaguerrePolynomialCoefficient(laguerreIndex: nat, polyPower: nat): real
{
  if laguerreIndex == 0 then
    if polyPower == 0 then 1.0 else 0.0
  else if laguerreIndex == 1 then
    if polyPower == 0 then 1.0
    else if polyPower == 1 then -1.0
    else 0.0
  else
    0.0
}

function SumLaguerreContributions(c: seq<real>, polyDegree: nat): real
  requires polyDegree < |c|
  decreases |c|
{
  if |c| == 0 then 0.0
  else if |c| == 1 then
    ConvertLaguerreCoefficient(c, 0, polyDegree)
  else
    ConvertLaguerreCoefficient(c, |c| - 1, polyDegree) + SumLaguerreContributions(c[..|c| - 1], polyDegree)
}

function BuildPolynomialCoeffs(c: seq<real>, idx: nat): seq<real>
  requires |c| > 0
  requires idx <= |c|
  ensures |BuildPolynomialCoeffs(c, idx)| == |c|
  decreases idx
{
  if idx == 0 then
    seq(|c|, i => 0.0)
  else
    var prev := BuildPolynomialCoeffs(c, idx - 1);
    seq(|c|, i => if i < idx then SumLaguerreContributions(c[..idx], i) else 0.0)
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
  if |c| == 1 {
    result := c;
  } else {
    result := seq(|c|, i => SumLaguerreContributions(c, i));
  }
}
// </vc-code>
