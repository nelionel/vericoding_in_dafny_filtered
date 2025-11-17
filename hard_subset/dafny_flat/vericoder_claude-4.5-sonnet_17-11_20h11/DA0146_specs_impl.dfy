// <vc-preamble>
function count_sf_flights(s: string): int
{
    if |s| <= 1 then 0
    else (if s[|s|-1] == 'F' && s[|s|-2] != 'F' then 1 else 0) + count_sf_flights(s[..|s|-1])
}

function count_fs_flights(s: string): int
{
    if |s| <= 1 then 0
    else (if s[|s|-1] == 'S' && s[|s|-2] != 'S' then 1 else 0) + count_fs_flights(s[..|s|-1])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: string)
    requires n >= 2
    requires |s| == n
    requires forall i :: 0 <= i < |s| ==> s[i] == 'S' || s[i] == 'F'
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> count_sf_flights(s) > count_fs_flights(s)
// </vc-spec>
// <vc-code>
{
  var sf_count := 0;
  var fs_count := 0;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant sf_count == count_sf_flights(s[..i])
    invariant fs_count == count_fs_flights(s[..i])
  {
    assert s[..i+1][..i] == s[..i];
    if s[i] == 'F' && s[i-1] != 'F' {
      sf_count := sf_count + 1;
    }
    if s[i] == 'S' && s[i-1] != 'S' {
      fs_count := fs_count + 1;
    }
    i := i + 1;
  }
  assert s[..n] == s;
  if sf_count > fs_count {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>
