// <vc-preamble>
function pow(base: int, exp: int): int
  requires exp >= 0
  ensures exp == 0 ==> pow(base, exp) == 1
  ensures exp > 0 && base > 0 ==> pow(base, exp) > 0
  ensures exp > 0 && base == 0 ==> pow(base, exp) == 0
{
  if exp == 0 then 1
  else base * pow(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>
lemma PowPositive(base: int, exp: int)
  requires exp >= 0
  requires base > 0
  ensures pow(base, exp) > 0
{
  if exp == 0 {
  } else {
    PowPositive(base, exp - 1);
  }
}

lemma PowIncreasing(base: int, exp: int)
  requires base >= 3
  requires exp >= 0
  ensures pow(base, exp + 1) >= 3 * pow(base, exp)
{
}

lemma GrowthLemma(a: int, b: int, y: int)
  requires 1 <= a <= b
  requires y >= 0
  requires a * pow(3, y) <= b * pow(2, y)
  ensures a * pow(3, y + 1) > b * pow(2, y + 1) || a * pow(3, y + 1) <= b * pow(2, y + 1)
{
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (years: int)
  requires 1 <= a <= b <= 10
  ensures years >= 0
  ensures a * pow(3, years) > b * pow(2, years)
  ensures years == 0 || a * pow(3, years - 1) <= b * pow(2, years - 1)
// </vc-spec>
// <vc-code>
{
  years := 0;
  PowPositive(2, 0);
  PowPositive(3, 0);
  
  while a * pow(3, years) <= b * pow(2, years)
    invariant years >= 0
    invariant a * pow(3, years) <= b * pow(2, years) ==> (years == 0 || a * pow(3, years - 1) <= b * pow(2, years - 1))
    decreases b * pow(2, years) - a * pow(3, years) + 1000
  {
    PowPositive(2, years + 1);
    PowPositive(3, years + 1);
    years := years + 1;
  }
}
// </vc-code>
