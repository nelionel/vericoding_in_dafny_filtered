// <vc-preamble>
predicate ValidInput(a: int, b: int, c: int, d: int) {
    a > 0 && b > 0 && c > 0 && d > 0
}

predicate IsValidFractionString(s: string, num: int, den: int) {
    num >= 0 && den > 0 && 
    gcd(num, den) == 1 &&
    s == intToString(num) + "/" + intToString(den)
}
// </vc-preamble>

// <vc-helpers>
function gcd(a: int, b: int): int
  requires a >= 0 && b >= 0
  requires a > 0 || b > 0
  decreases a + b
{
  if a == 0 then b
  else if b == 0 then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

function abs(x: int): int
{
  if x >= 0 then x else -x
}

/* helper modified by LLM (iteration 2): fixed decreases clause for negative numbers */
function intToString(n: int): string
  decreases abs(n)
{
  if n == 0 then "0"
  else if n > 0 then
    if n < 10 then [digitToChar(n)]
    else intToString(n / 10) + [digitToChar(n % 10)]
  else "-" + intToString(abs(n))
}

function digitToChar(d: int): char
  requires 0 <= d < 10
{
  if d == 0 then '0'
  else if d == 1 then '1'
  else if d == 2 then '2'
  else if d == 3 then '3'
  else if d == 4 then '4'
  else if d == 5 then '5'
  else if d == 6 then '6'
  else if d == 7 then '7'
  else if d == 8 then '8'
  else '9'
}

lemma gcdPositive(a: int, b: int)
  requires a > 0 || b > 0
  requires a >= 0 && b >= 0
  ensures gcd(a, b) > 0
  decreases a + b
{
  if a == 0 {}
  else if b == 0 {}
  else if a > b { gcdPositive(a - b, b); }
  else { gcdPositive(a, b - a); }
}

/* helper modified by LLM (iteration 2): added witnesses to prove postconditions */
lemma gcdDivides(a: int, b: int)
  requires a >= 0 && b >= 0
  requires a > 0 || b > 0
  ensures exists k :: a == gcd(a, b) * k
  ensures exists k :: b == gcd(a, b) * k
  decreases a + b
{
  if a == 0 {
    assert b == gcd(a, b) * 1;
    assert a == gcd(a, b) * 0;
  }
  else if b == 0 {
    assert a == gcd(a, b) * 1;
    assert b == gcd(a, b) * 0;
  }
  else if a > b { gcdDivides(a - b, b); }
  else { gcdDivides(a, b - a); }
}

/* helper modified by LLM (iteration 2): added lemma to prove gcd property after division */
lemma gcdAfterDivision(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a / gcd(a, b), b / gcd(a, b)) == 1
{
  var g := gcd(a, b);
  gcdPositive(a, b);
  gcdDivides(a, b);
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, d: int) returns (result: string)
    requires ValidInput(a, b, c, d)
    ensures a * d == b * c ==> result == "0/1"
    ensures a * d > b * c ==> exists numerator, denominator :: 
        numerator > 0 && denominator > 0 && 
        gcd(numerator, denominator) == 1 &&
        result == intToString(numerator) + "/" + intToString(denominator) &&
        numerator * a * d == (a * d - b * c) * denominator
    ensures a * d < b * c ==> exists numerator, denominator :: 
        numerator > 0 && denominator > 0 && 
        gcd(numerator, denominator) == 1 &&
        result == intToString(numerator) + "/" + intToString(denominator) &&
        numerator * b * c == (b * c - a * d) * denominator
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added lemma calls and assertions to prove postconditions */
{
  var ad := a * d;
  var bc := b * c;
  
  if ad == bc {
    result := "0/1";
  } else if ad > bc {
    var diff := ad - bc;
    var g := gcd(diff, ad);
    gcdPositive(diff, ad);
    gcdDivides(diff, ad);
    gcdAfterDivision(diff, ad);
    var num := diff / g;
    var den := ad / g;
    result := intToString(num) + "/" + intToString(den);
    assert num * ad == diff * den;
  } else {
    var diff := bc - ad;
    var g := gcd(diff, bc);
    gcdPositive(diff, bc);
    gcdDivides(diff, bc);
    gcdAfterDivision(diff, bc);
    var num := diff / g;
    var den := bc / g;
    result := intToString(num) + "/" + intToString(den);
    assert num * bc == diff * den;
  }
}
// </vc-code>
