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
/* helper modified by LLM (iteration 3): fixed GcdDivides proof and DivisionPreservesGcd to prove gcd property */
function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases a + b
{
  if a == b then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

lemma GcdDivides(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0
  ensures b % gcd(a, b) == 0
  decreases a + b
{
  var g := gcd(a, b);
  if a == b {
    assert g == a;
  } else if a > b {
    GcdDivides(a - b, b);
    var g' := gcd(a - b, b);
    assert g == g';
    assert (a - b) % g' == 0;
    assert b % g' == 0;
    assert a % g == 0;
  } else {
    GcdDivides(a, b - a);
    var g' := gcd(a, b - a);
    assert g == g';
    assert a % g' == 0;
    assert (b - a) % g' == 0;
    assert b % g == 0;
  }
}

lemma GcdProperties(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
  ensures gcd(a, b) <= a
  ensures gcd(a, b) <= b
  decreases a + b
{
  if a == b {
  } else if a > b {
    GcdProperties(a - b, b);
  } else {
    GcdProperties(a, b - a);
  }
}

lemma DivisionPreservesGcd(a: int, b: int, g: int)
  requires a > 0 && b > 0 && g > 0
  requires a % g == 0
  requires b % g == 0
  requires g == gcd(a, b)
  ensures a / g > 0
  ensures b / g > 0
  ensures gcd(a / g, b / g) == 1
  decreases a + b
{
  var a' := a / g;
  var b' := b / g;
  assert a' > 0;
  assert b' > 0;
  
  if a' == b' {
    assert gcd(a', b') == a';
    assert a == a' * g;
    assert b == b' * g;
    assert a == b;
    assert g == a;
    assert a' == 1;
    assert gcd(a', b') == 1;
  } else {
    GcdIsOne(a', b', a, b, g);
  }
}

lemma GcdIsOne(a': int, b': int, a: int, b: int, g: int)
  requires a' > 0 && b' > 0
  requires a > 0 && b > 0 && g > 0
  requires a == a' * g
  requires b == b' * g
  requires g == gcd(a, b)
  ensures gcd(a', b') == 1
  decreases a' + b'
{
  var d := gcd(a', b');
  if d > 1 {
    GcdDivides(a', b');
    assert a' % d == 0;
    assert b' % d == 0;
    var k1 := a' / d;
    var k2 := b' / d;
    assert a == k1 * d * g;
    assert b == k2 * d * g;
    var dg := d * g;
    assert a % dg == 0;
    assert b % dg == 0;
    assert dg > g;
    GcdProperties(a, b);
    assert g <= a && g <= b;
    assert dg <= a || dg <= b;
    GcdLowerBound(a, b, g, dg);
  }
}

lemma GcdLowerBound(a: int, b: int, g: int, dg: int)
  requires a > 0 && b > 0
  requires g > 0 && dg > g
  requires a % g == 0 && b % g == 0
  requires a % dg == 0 && b % dg == 0
  requires g == gcd(a, b)
  ensures false
{
  GcdDivides(a, b);
  CommonDivisorLemma(a, b, dg);
}

lemma CommonDivisorLemma(a: int, b: int, d: int)
  requires a > 0 && b > 0 && d > 0
  requires a % d == 0 && b % d == 0
  ensures d <= gcd(a, b)
  decreases a + b
{
  var g := gcd(a, b);
  if a == b {
    assert g == a;
    assert d <= a;
  } else if a > b {
    assert g == gcd(a - b, b);
    assert (a - b) % d == 0;
    CommonDivisorLemma(a - b, b, d);
  } else {
    assert g == gcd(a, b - a);
    assert (b - a) % d == 0;
    CommonDivisorLemma(a, b - a, d);
  }
}

lemma DivisionMaintainsOrder(a: int, b: int, g: int)
  requires a > 0 && b > 0 && g > 0
  requires a % g == 0
  requires b % g == 0
  requires a <= b
  ensures a / g <= b / g
{
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
  /* code modified by LLM (iteration 3): added lemma calls to prove gcd property */
  var totalDraws := t + w;
  var whiteDraws := w;
  
  GcdProperties(whiteDraws, totalDraws);
  var g := gcd(whiteDraws, totalDraws);
  
  GcdDivides(whiteDraws, totalDraws);
  assert g > 0;
  assert whiteDraws % g == 0;
  assert totalDraws % g == 0;
  
  numerator := whiteDraws / g;
  denominator := totalDraws / g;
  
  assert numerator > 0;
  assert denominator > 0;
  
  DivisionMaintainsOrder(whiteDraws, totalDraws, g);
  assert numerator <= denominator;
  
  DivisionPreservesGcd(whiteDraws, totalDraws, g);
  assert gcd(numerator, denominator) == 1;
}
// </vc-code>
