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
  requires a >= 0 && b >= 0
  decreases a + b
{
  if a == 0 then b
  else if b == 0 then a
  else if a < b then gcd(a, b - a)
  else gcd(a - b, b)
}

lemma gcd_commutative(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures gcd(a, b) == gcd(b, a)
  decreases a + b
{
}

lemma gcd_divides(a: int, b: int, d: int)
  requires a >= 0 && b >= 0
  requires d == gcd(a, b)
  ensures d > 0 ==> (exists k: int :: a == k * d) && (exists m: int :: b == m * d)
{
}

function abs(x: int): int
{
  if x >= 0 then x else -x
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
  var totalBalls := t + w + b;
  var favorable := t + w;
  
  var g := gcd(favorable, totalBalls);
  
  numerator := favorable / g;
  denominator := totalBalls / g;
}
// </vc-code>
