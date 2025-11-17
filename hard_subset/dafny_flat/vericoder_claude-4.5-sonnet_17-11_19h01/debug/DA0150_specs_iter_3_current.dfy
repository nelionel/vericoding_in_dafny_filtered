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

/* helper modified by LLM (iteration 3): fixed decreases clause to use n instead of abs(n) for recursion */
function intToString(n: int): string
  decreases if n >= 0 then n else -n
{
  if n == 0 then "0"
  else if n > 0 then
    if n < 10 then [digitToChar(n)]
    else intToString(n / 10) + [digitToChar(n % 10)]
  else "-" + intToString(-n)
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

/* helper modified by LLM (iteration 3): added explicit witnesses for recursive cases */
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
  else if a > b { 
    gcdDivides(a - b, b);
    var g := gcd(a - b, b);
    var k1 :| (a - b) == g * k1;
    var k2 :| b == g * k2;
    assert a == g * (k1 + k2);
  }
  else { 
    gcdDivides(a, b - a);
    var g := gcd(a, b - a);
    var k1 :| a == g * k1;
    var k2 :| (b - a) == g * k2;
    assert b == g * (k1 + k2);
  }
}

/* helper modified by LLM (iteration 3): simplified to remove precondition errors */
lemma gcdAfterDivision(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
  ensures a / gcd(a, b) >= 0
  ensures b / gcd(a, b) > 0
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
/* code modified by LLM (iteration 3): simplified lemma calls and fixed postcondition proofs */
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
    var num := diff / g;
    var den := ad / g;
    result := intToString(num) + "/" + intToString(den);
    assert gcd(num, den) == 1 by {
      gcdAfterDivision(diff, ad);
    }
    assert num * ad == diff * den;
  } else {
    var diff := bc - ad;
    var g := gcd(diff, bc);
    gcdPositive(diff, bc);
    gcdDivides(diff, bc);
    var num := diff / g;
    var den := bc / g;
    result := intToString(num) + "/" + intToString(den);
    assert gcd(num, den) == 1 by {
      gcdAfterDivision(diff, bc);
    }
    assert num * bc == diff * den;
  }
}
// </vc-code>
