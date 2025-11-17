// <vc-preamble>
function count_negative_temp_days(temps: seq<int>): int
{
    if |temps| == 0 then 0
    else (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed lemma to handle base case properly */
lemma NegativeTempImpliesPositiveCount(temps: seq<int>, idx: int)
  requires 0 <= idx < |temps|
  requires temps[idx] < 0
  ensures count_negative_temp_days(temps) > 0
{
  if idx == 0 {
    assert temps[0] < 0;
    assert count_negative_temp_days(temps) == 1 + count_negative_temp_days(temps[1..]);
    assert count_negative_temp_days(temps) >= 1;
  } else {
    NegativeTempImpliesPositiveCount(temps[1..], idx - 1);
    assert count_negative_temp_days(temps[1..]) > 0;
    assert count_negative_temp_days(temps) == (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..]);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, temps: seq<int>) returns (result: int)
  requires n >= 1
  requires k >= 0 && k <= n
  requires |temps| == n
  requires forall i :: 0 <= i < n ==> -20 <= temps[i] <= 20
  ensures result == -1 <==> count_negative_temp_days(temps) > k
  ensures result != -1 ==> result >= 0
  ensures result == 0 ==> forall i :: 0 <= i < n ==> temps[i] >= 0
  ensures result > 0 ==> exists i :: 0 <= i < n && temps[i] < 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed invariant to properly track non-negative prefix */
  var neg_count := count_negative_temp_days(temps);
  
  if neg_count > k {
    result := -1;
  } else {
    result := 0;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant result >= 0
      invariant result == 0 ==> forall j :: 0 <= j < i ==> temps[j] >= 0
      invariant result > 0 ==> 0 <= result < n && temps[result] < 0
      invariant result > 0 ==> forall j :: result < j < i ==> temps[j] >= 0
    {
      if temps[i] < 0 {
        result := i;
      }
      i := i + 1;
    }
  }
}
// </vc-code>
