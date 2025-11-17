// <vc-preamble>
predicate ValidInput(y: int)
{
    1000 <= y <= 9000
}

function HasDistinctDigits(n: int): bool
{
    var digits := NumberToDigits(n);
    AllDistinct(digits)
}

function NumberToDigits(n: int): seq<int>
{
    if n == 0 then [0]
    else if n > 0 then NumberToDigitsHelper(n, [])
    else NumberToDigitsHelper(-n, [])
}

function NumberToDigitsHelper(n: int, acc: seq<int>): seq<int>
requires n >= 0
decreases n
{
    if n == 0 then acc
    else NumberToDigitsHelper(n / 10, [n % 10] + acc)
}

predicate AllDistinct(digits: seq<int>)
{
    forall i, j :: 0 <= i < j < |digits| ==> digits[i] != digits[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added lemmas to prove digit properties */
lemma DistinctDigitsImpliesAllDistinct(n: int)
  requires HasDistinctDigits(n)
  ensures AllDistinct(NumberToDigits(n))
{
}

lemma NumberToDigitsLength(n: int)
  requires n >= 1000 && n <= 9876
  ensures |NumberToDigits(n)| == 4
{
  var digits := NumberToDigits(n);
  assert digits == NumberToDigitsHelper(n, []);
  NumberToDigitsHelperLength(n, []);
}

lemma NumberToDigitsHelperLength(n: int, acc: seq<int>)
  requires n >= 1000 && n <= 9876
  requires |acc| == 0
  ensures |NumberToDigitsHelper(n, acc)| == 4
  decreases n
{
  if n == 0 {
  } else {
    NumberToDigitsHelperLength(n / 10, [n % 10] + acc);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(y: int) returns (result: int)
requires ValidInput(y)
ensures result > y
ensures HasDistinctDigits(result)
ensures forall n :: y < n < result ==> !HasDistinctDigits(n)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): added assertion to help prove HasDistinctDigits */
  result := y + 1;
  while result <= 9876 && !HasDistinctDigits(result)
    invariant result > y
    invariant result <= 9877
    invariant forall n :: y < n < result ==> !HasDistinctDigits(n)
    decreases 9876 - result
  {
    result := result + 1;
  }
  assert result > y;
  assert result <= 9877;
  assert HasDistinctDigits(result) || result > 9876;
  if result > 9876 {
    result := 9877;
  }
  var digits := NumberToDigits(result);
  assert AllDistinct(digits);
}
// </vc-code>
