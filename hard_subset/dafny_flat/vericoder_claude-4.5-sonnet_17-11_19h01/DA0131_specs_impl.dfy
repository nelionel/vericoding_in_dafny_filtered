// <vc-preamble>
function count_negative_temp_days(temps: seq<int>): int
{
    if |temps| == 0 then 0
    else (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed lemma proof by establishing proper sequence relationship */
lemma CountNegativeExtend(temps: seq<int>, i: int)
  requires 0 <= i < |temps|
  ensures count_negative_temp_days(temps[..i+1]) == count_negative_temp_days(temps[..i]) + (if temps[i] < 0 then 1 else 0)
{
  if i == 0 {
    assert temps[..1] == [temps[0]];
    assert count_negative_temp_days(temps[..1]) == (if temps[0] < 0 then 1 else 0);
    assert temps[..0] == [];
    assert count_negative_temp_days(temps[..0]) == 0;
  } else {
    assert temps[..i+1][0] == temps[0];
    assert temps[..i+1][1..] == temps[1..i+1];
    assert temps[..i][0] == temps[0];
    assert temps[..i][1..] == temps[1..i];
    CountNegativeExtend(temps[1..], i-1);
    assert count_negative_temp_days(temps[1..i+1]) == count_negative_temp_days(temps[1..i]) + (if temps[i] < 0 then 1 else 0);
  }
}

lemma CountNegativeZeroImpliesAllNonNegative(temps: seq<int>)
  requires count_negative_temp_days(temps) == 0
  ensures forall j :: 0 <= j < |temps| ==> temps[j] >= 0
{
  if |temps| > 0 {
    assert (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..]) == 0;
    assert temps[0] >= 0;
    assert count_negative_temp_days(temps[1..]) == 0;
    CountNegativeZeroImpliesAllNonNegative(temps[1..]);
  }
}

lemma CountNegativePositiveImpliesExists(temps: seq<int>)
  requires count_negative_temp_days(temps) > 0
  ensures exists j :: 0 <= j < |temps| && temps[j] < 0
{
  if |temps| > 0 {
    if temps[0] < 0 {
      assert temps[0] < 0;
    } else {
      assert count_negative_temp_days(temps[1..]) > 0;
      CountNegativePositiveImpliesExists(temps[1..]);
      var j :| 0 <= j < |temps[1..]| && temps[1..][j] < 0;
      assert temps[j+1] < 0;
    }
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
/* code modified by LLM (iteration 3): added lemma call in loop to maintain invariant */
{
  var neg_count := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant neg_count == count_negative_temp_days(temps[..i])
  {
    CountNegativeExtend(temps, i);
    if temps[i] < 0 {
      neg_count := neg_count + 1;
    }
    i := i + 1;
  }
  
  assert temps[..n] == temps;
  
  if neg_count > k {
    result := -1;
  } else {
    result := neg_count;
    if result == 0 {
      CountNegativeZeroImpliesAllNonNegative(temps);
    }
    if result > 0 {
      CountNegativePositiveImpliesExists(temps);
    }
  }
}
// </vc-code>
