// <vc-preamble>
function power(base: int, exp: int): int
    requires exp >= 0
    ensures exp == 0 ==> power(base, exp) == 1
    ensures base > 0 ==> power(base, exp) > 0
    ensures base != 0 ==> power(base, exp) != 0
    decreases exp
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): simplified gcd and lcm without complex verification */
function gcd(a: int, b: int): int
    requires a > 0 && b >= 0
    decreases b
{
    if b == 0 then a else gcd(b, a % b)
}

function lcm(a: int, b: int): int
    requires a > 0 && b > 0
{
    (a * b) / gcd(a, b)
}

lemma GcdDivides(a: int, b: int)
    requires a > 0 && b >= 0
    ensures var g := gcd(a, b); g > 0 && a % g == 0 && (b == 0 || b % g == 0)
    decreases b
{
    if b == 0 {
    } else {
        GcdDivides(b, a % b);
    }
}

lemma LcmProperties(a: int, b: int)
    requires a > 0 && b > 0
    ensures var l := lcm(a, b); l > 0 && l % a == 0 && l % b == 0
{
    GcdDivides(a, b);
    var g := gcd(a, b);
    var l := lcm(a, b);
    assert l == (a * b) / g;
}

lemma LcmIsMinimal(a: int, b: int, m: int)
    requires a > 0 && b > 0
    requires m > 0 && m % a == 0 && m % b == 0
    ensures lcm(a, b) <= m
{
    GcdDivides(a, b);
    var g := gcd(a, b);
    var l := lcm(a, b);
    var qa := a / g;
    var qb := b / g;
    assert a == qa * g;
    assert b == qb * g;
    assert l == qa * b;
    assert l == qb * a;
    var km := m / a;
    assert m == km * a;
    assert m % b == 0;
    assert (km * a) % b == 0;
    assert km * a % b == 0;
    assert (km * qa * g) % (qb * g) == 0;
    assert (km * qa) % qb == 0;
    assert l == qb * a;
    assert l <= m;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires n > 0 && k >= 0
    ensures result > 0
    ensures result % n == 0
    ensures result % power(10, k) == 0
    ensures forall m :: m > 0 && m % n == 0 && m % power(10, k) == 0 ==> result <= m
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute LCM with lemma invocations */
  var powerOf10 := power(10, k);
  LcmProperties(n, powerOf10);
  result := lcm(n, powerOf10);
  forall m | m > 0 && m % n == 0 && m % powerOf10 == 0
    ensures result <= m
  {
    LcmIsMinimal(n, powerOf10, m);
  }
}
// </vc-code>
