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
/* helper modified by LLM (iteration 2): added lemmas for gcd properties and division correctness */
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
  if a == b {
  } else if a > b {
    GcdDivides(a - b, b);
  } else {
    GcdDivides(a, b - a);
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
{
  GcdDivides(a, b);
  var a' := a / g;
  var b' := b / g;
  assert a' > 0;
  assert b' > 0;
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
  /* code modified by LLM (iteration 2): added lemma calls and assertions to prove postconditions */
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
