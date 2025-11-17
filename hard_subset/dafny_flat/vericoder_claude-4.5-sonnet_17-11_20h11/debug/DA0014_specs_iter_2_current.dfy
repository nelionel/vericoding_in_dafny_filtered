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
/* helper modified by LLM (iteration 2): Added proper implementation of gcd function and lemmas to prove divisibility properties */
function gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
  decreases a + b
{
  if a == 0 then b
  else if b == 0 then a
  else if a < b then gcd(a, b - a)
  else gcd(a - b, b)
}

lemma gcd_divides_both(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures var d := gcd(a, b); d > 0 ==> (exists k: int :: a == k * d) && (exists m: int :: b == m * d)
  decreases a + b
{
  var d := gcd(a, b);
  if a == 0 {
    assert a == 0 * d;
    assert b == 1 * d;
  } else if b == 0 {
    assert a == 1 * d;
    assert b == 0 * d;
  } else if a < b {
    gcd_divides_both(a, b - a);
  } else {
    gcd_divides_both(a - b, b);
  }
}

lemma gcd_positive(a: int, b: int)
  requires a > 0 || b > 0
  requires a >= 0 && b >= 0
  ensures gcd(a, b) > 0
  decreases a + b
{
  if a == 0 {
  } else if b == 0 {
  } else if a < b {
    gcd_positive(a, b - a);
  } else {
    gcd_positive(a - b, b);
  }
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
  /* code modified by LLM (iteration 2): Added proper division after gcd calculation with lemmas to ensure postconditions */
  var totalBalls := t + w + b;
  var favorable := t + w;
  
  var g := gcd(favorable, totalBalls);
  
  gcd_positive(favorable, totalBalls);
  gcd_divides_both(favorable, totalBalls);
  
  assert g > 0;
  
  numerator := favorable / g;
  denominator := totalBalls / g;
  
  assert numerator >= 0;
  assert denominator > 0;
  assert numerator <= denominator;
  assert gcd(numerator, denominator) == 1;
}
// </vc-code>
