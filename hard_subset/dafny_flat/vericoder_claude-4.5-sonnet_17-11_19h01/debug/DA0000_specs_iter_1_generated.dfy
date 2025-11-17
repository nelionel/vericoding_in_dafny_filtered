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

// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
  requires ValidInput(x)
  ensures ValidResult(x, result)
// </vc-spec>
// <vc-code>
{
  var maxSum := 0;
  result := 1;
  var i := 1;
  while i <= x
    invariant 1 <= i <= x + 1
    invariant result > 0 && result < i
    invariant maxSum == digitSum(intToDigits(result))
    invariant forall y :: 1 <= y < i ==> digitSum(intToDigits(y)) <= maxSum
    invariant forall y :: 1 <= y < i && digitSum(intToDigits(y)) == maxSum ==> y <= result
  {
    var currentSum := digitSum(intToDigits(i));
    if currentSum > maxSum || (currentSum == maxSum && i > result) {
      maxSum := currentSum;
      result := i;
    }
    i := i + 1;
  }
}
// </vc-code>
