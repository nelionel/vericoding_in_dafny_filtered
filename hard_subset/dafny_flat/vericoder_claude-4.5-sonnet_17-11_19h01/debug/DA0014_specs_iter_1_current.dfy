// <vc-preamble>
predicate ValidInput(t: int, w: int, b: int)
{
  t > 0 && w > 0 && b > 0
}

predicate ValidFraction(numerator: int, denominator: int)
{
  numerator >= 0 && denominator > 0 && numerator <= denominator
}

predicate IsIrreducibleFraction(numerator: int, denominator: int)
  requires ValidFraction(numerator, denominator)
{
  gcd(numerator, denominator) == 1
}
// </vc-preamble>

// <vc-helpers>
function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases a + b
{
  if a == b then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

function abs(x: int): int
{
  if x >= 0 then x else -x
}

function gcdGeneral(a: int, b: int): int
  requires a > 0 || b > 0
{
  if a == 0 then b
  else if b == 0 then a
  else if a > 0 && b > 0 then gcd(a, b)
  else if a > 0 then a
  else b
}
// </vc-helpers>

// <vc-spec>
method solve(t: int, w: int, b: int) returns (numerator: int, denominator: int)
  requires ValidInput(t, w, b)
  ensures ValidFraction(numerator, denominator)
  ensures IsIrreducibleFraction(numerator, denominator)
// </vc-spec>
// <vc-code>
{
  var totalDraws := t + w;
  var whiteDraws := w;
  var g := gcd(whiteDraws, totalDraws);
  numerator := whiteDraws / g;
  denominator := totalDraws / g;
}
// </vc-code>
