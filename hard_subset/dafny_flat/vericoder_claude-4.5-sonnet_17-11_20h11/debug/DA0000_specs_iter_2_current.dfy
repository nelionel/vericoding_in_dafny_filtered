// <vc-preamble>
function intToDigits(x: int): seq<int>
  requires x >= 0
{
  if x == 0 then [0]
  else intToDigitsHelper(x)
}

function intToDigitsHelper(x: int): seq<int>
  requires x > 0
  decreases x
{
  if x < 10 then [x]
  else intToDigitsHelper(x / 10) + [x % 10]
}

function digitSum(digits: seq<int>): int
{
  if |digits| == 0 then 0
  else digits[0] + digitSum(digits[1..])
}

predicate ValidInput(x: int)
{
  x >= 1
}

predicate ValidResult(x: int, result: int)
  requires ValidInput(x)
{
  result > 0 &&
  result <= x &&
  (forall y :: 1 <= y <= x ==> digitSum(intToDigits(y)) <= digitSum(intToDigits(result))) &&
  (forall y :: 1 <= y <= x && digitSum(intToDigits(y)) == digitSum(intToDigits(result)) ==> y <= result)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added proof body for DigitSumMonotonic */
lemma DigitSumMonotonic(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures digitSum(intToDigits(a)) >= 0 && digitSum(intToDigits(b)) >= 0
{
  DigitSumNonNegative(a);
  DigitSumNonNegative(b);
}

/* helper modified by LLM (iteration 2): added DigitSumNonNegative lemma */
lemma DigitSumNonNegative(x: int)
  requires x >= 0
  ensures digitSum(intToDigits(x)) >= 0
  decreases x
{
  if x == 0 {
    assert intToDigits(0) == [0];
  } else {
    DigitSumHelperNonNegative(x);
  }
}

lemma DigitSumHelperNonNegative(x: int)
  requires x > 0
  ensures digitSum(intToDigitsHelper(x)) >= 0
  decreases x
{
  if x < 10 {
    assert intToDigitsHelper(x) == [x];
    assert digitSum([x]) == x;
  } else {
    DigitSumHelperNonNegative(x / 10);
    var prefix := intToDigitsHelper(x / 10);
    var lastDigit := x % 10;
    assert lastDigit >= 0;
    assert digitSum(prefix) >= 0;
  }
}

/* helper modified by LLM (iteration 2): added proof body for DigitSumPositive */
lemma DigitSumPositive(x: int)
  requires x >= 1
  ensures digitSum(intToDigits(x)) >= 1
  decreases x
{
  assert intToDigits(x) == intToDigitsHelper(x);
  DigitSumHelperPositive(x);
}

lemma DigitSumHelperPositive(x: int)
  requires x > 0
  ensures digitSum(intToDigitsHelper(x)) >= 1
  decreases x
{
  if x < 10 {
    assert intToDigitsHelper(x) == [x];
    assert digitSum([x]) == x >= 1;
  } else {
    DigitSumHelperPositive(x / 10);
  }
}

lemma ResultValid(maxVal: int, maxDigitSum: int, maxNum: int)
  requires maxNum >= 1 && maxNum <= maxVal
  requires forall y :: 1 <= y <= maxVal ==> digitSum(intToDigits(y)) <= maxDigitSum
  requires digitSum(intToDigits(maxNum)) == maxDigitSum
  requires forall y :: 1 <= y <= maxVal && digitSum(intToDigits(y)) == maxDigitSum ==> y <= maxNum
  ensures ValidInput(maxVal) ==> ValidResult(maxVal, maxNum)
{
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
  requires ValidInput(x)
  ensures ValidResult(x, result)
// </vc-spec>
// <vc-code>
{
  var i := 1;
  var maxDigitSum := digitSum(intToDigits(1));
  var maxNum := 1;
  
  while i < x
    invariant 1 <= i <= x
    invariant maxNum >= 1 && maxNum <= i
    invariant maxDigitSum == digitSum(intToDigits(maxNum))
    invariant forall y :: 1 <= y <= i ==> digitSum(intToDigits(y)) <= maxDigitSum
    invariant forall y :: 1 <= y <= i && digitSum(intToDigits(y)) == maxDigitSum ==> y <= maxNum
  {
    i := i + 1;
    var currentDigitSum := digitSum(intToDigits(i));
    
    if currentDigitSum > maxDigitSum {
      maxDigitSum := currentDigitSum;
      maxNum := i;
    } else if currentDigitSum == maxDigitSum {
      if i > maxNum {
        maxNum := i;
      }
    }
  }
  
  result := maxNum;
}
// </vc-code>
