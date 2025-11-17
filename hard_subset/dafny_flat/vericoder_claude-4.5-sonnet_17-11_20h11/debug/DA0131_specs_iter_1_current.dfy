// <vc-preamble>
function count_negative_temp_days(temps: seq<int>): int
{
    if |temps| == 0 then 0
    else (if temps[0] < 0 then 1 else 0) + count_negative_temp_days(temps[1..])
}
// </vc-preamble>

// <vc-helpers>

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
      invariant result > 0 ==> exists j :: 0 <= j < i && temps[j] < 0
    {
      if temps[i] < 0 {
        result := i;
      }
      i := i + 1;
    }
  }
}
// </vc-code>
