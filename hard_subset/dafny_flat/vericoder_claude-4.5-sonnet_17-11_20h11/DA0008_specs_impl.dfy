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
/* helper modified by LLM (iteration 3): Simplified lemmas to avoid timeouts */
lemma countMonotonic(n: int, m: int, target1: int, target2: int)
  requires n >= 1 && m >= 1 && target1 >= 0 && target2 >= 0
  requires target1 <= target2
  ensures countLessOrEqualValue(n, m, target1) <= countLessOrEqualValue(n, m, target2)
  decreases target2 - target1
{
  if target1 <= 0 && target2 <= 0 {
  } else if target1 <= 0 && target2 > 0 {
  } else if target2 >= n * m {
  } else if target1 >= n * m {
  } else {
    if target1 < target2 {
      countMonotonic(n, m, target1, target2 - 1);
    }
  }
}

lemma countLessOrEqualBounds(n: int, m: int, target: int)
  requires n >= 1 && m >= 1 && target >= 1
  ensures target >= n * m ==> countLessOrEqualValue(n, m, target) == n * m
  ensures target == 1 ==> countLessOrEqualValue(n, m, target) <= 1
{
  if target == 1 {
    countLessValueAtTwo(n, m);
  }
}

lemma countLessValueAtTwo(n: int, m: int)
  requires n >= 1 && m >= 1
  ensures countLessValue(n, m, 2) <= 1
  decreases n
{
  if n == 1 {
    var maxJ := (2 - 1) / 1;
    assert maxJ == 1;
    var actualMaxJ := if maxJ > m then m else maxJ;
    assert actualMaxJ == 1;
    countLessValue(0, m, 2);
  } else {
    var maxJ := (2 - 1) / n;
    assert maxJ == 0;
    var actualMaxJ := if maxJ > m then m else maxJ;
    assert actualMaxJ == 0;
    var contribution := if actualMaxJ >= 1 then actualMaxJ else 0;
    assert contribution == 0;
    countLessValueAtTwo(n - 1, m);
  }
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
/* code modified by LLM (iteration 3): Added lemma calls to establish properties */
{
  var low := 1;
  var high := n * m;
  countLessOrEqualBounds(n, m, n * m);
  
  while low < high
    invariant 1 <= low <= high <= n * m
    invariant countLessOrEqualValue(n, m, high) >= k
    invariant low == 1 || countLessOrEqualValue(n, m, low - 1) < k
  {
    var mid := low + (high - low) / 2;
    var count := countLessOrEqualValue(n, m, mid);
    
    if count < k {
      low := mid + 1;
    } else {
      countMonotonic(n, m, mid, high);
      high := mid;
    }
  }
  
  result := low;
}
// </vc-code>
