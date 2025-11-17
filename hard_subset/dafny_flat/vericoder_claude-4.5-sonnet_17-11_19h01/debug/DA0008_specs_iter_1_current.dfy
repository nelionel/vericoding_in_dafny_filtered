// <vc-preamble>
function countLessValue(n: int, m: int, target: int): int
  requires n >= 0 && m >= 1 && target >= 1
  ensures countLessValue(n, m, target) >= 0
  ensures countLessValue(n, m, target) <= n * m
{
  if n == 0 then 0
  else 
    var maxJ := (target - 1) / n;
    var actualMaxJ := if maxJ > m then m else maxJ;
    var contribution := if actualMaxJ >= 1 then actualMaxJ else 0;
    contribution + countLessValue(n - 1, m, target)
}

function countLessOrEqualValue(n: int, m: int, target: int): int
  requires n >= 1 && m >= 1 && target >= 0
  ensures countLessOrEqualValue(n, m, target) >= 0
  ensures countLessOrEqualValue(n, m, target) <= n * m
{
  if target <= 0 then 0
  else if target >= n * m then n * m
  else countLessValue(n, m, target + 1)
}

predicate ValidInput(n: int, m: int, k: int)
{
  1 <= n <= 500000 && 1 <= m <= 500000 && 1 <= k <= n * m
}
// </vc-preamble>

// <vc-helpers>
function countMonotonic(n: int, m: int, target: int): int
  requires n >= 0 && m >= 1 && target >= 1
  ensures countMonotonic(n, m, target) == countLessValue(n, m, target)
{
  countLessValue(n, m, target)
}

lemma CountIncreases(n: int, m: int, t1: int, t2: int)
  requires n >= 1 && m >= 1 && 1 <= t1 < t2
  ensures countLessOrEqualValue(n, m, t1) <= countLessOrEqualValue(n, m, t2)
{
}

lemma CountAtKthElement(n: int, m: int, k: int, val: int)
  requires ValidInput(n, m, k)
  requires 1 <= val <= n * m
  requires countLessOrEqualValue(n, m, val) >= k
  requires val == 1 || countLessOrEqualValue(n, m, val - 1) < k
  ensures countLessOrEqualValue(n, m, val) >= k
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int) returns (result: int)
  requires ValidInput(n, m, k)
  ensures 1 <= result <= n * m
  ensures countLessOrEqualValue(n, m, result) >= k
  ensures result == 1 || countLessOrEqualValue(n, m, result - 1) < k
// </vc-spec>
// <vc-code>
{
  var low := 1;
  var high := n * m;
  result := 1;
  
  while low <= high
    invariant 1 <= low <= n * m + 1
    invariant 1 <= high <= n * m
    invariant 1 <= result <= n * m
    invariant low > 1 ==> countLessOrEqualValue(n, m, low - 1) < k
    invariant high < n * m ==> countLessOrEqualValue(n, m, high + 1) >= k
    invariant countLessOrEqualValue(n, m, result) >= k
    invariant result == 1 || countLessOrEqualValue(n, m, result - 1) < k
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    var count := countLessOrEqualValue(n, m, mid);
    
    if count >= k {
      result := mid;
      high := mid - 1;
    } else {
      low := mid + 1;
    }
  }
}
// </vc-code>
