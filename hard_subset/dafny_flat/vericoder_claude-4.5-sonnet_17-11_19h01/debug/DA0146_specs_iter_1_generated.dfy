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
function count_sf_flights_iterative(s: string, idx: int): int
    requires 0 <= idx <= |s|
    decreases |s| - idx
{
    if idx >= |s| - 1 then 0
    else (if s[idx] == 'S' && s[idx+1] == 'F' then 1 else 0) + count_sf_flights_iterative(s, idx + 1)
}

function count_fs_flights_iterative(s: string, idx: int): int
    requires 0 <= idx <= |s|
    decreases |s| - idx
{
    if idx >= |s| - 1 then 0
    else (if s[idx] == 'F' && s[idx+1] == 'S' then 1 else 0) + count_fs_flights_iterative(s, idx + 1)
}

lemma count_sf_equivalence(s: string, idx: int)
    requires 0 <= idx <= |s|
    ensures count_sf_flights_iterative(s, idx) == count_sf_flights(s[idx..])
{
    if idx >= |s| - 1 {
    } else {
        count_sf_equivalence(s, idx + 1);
    }
}

lemma count_fs_equivalence(s: string, idx: int)
    requires 0 <= idx <= |s|
    ensures count_fs_flights_iterative(s, idx) == count_fs_flights(s[idx..])
{
    if idx >= |s| - 1 {
    } else {
        count_fs_equivalence(s, idx + 1);
    }
}
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
    var i := 0;
    
    while i < n - 1
        invariant 0 <= i <= n - 1
        invariant sf_count == count_sf_flights_iterative(s, 0) - count_sf_flights_iterative(s, i)
        invariant fs_count == count_fs_flights_iterative(s, 0) - count_fs_flights_iterative(s, i)
    {
        if s[i] == 'S' && s[i+1] == 'F' {
            sf_count := sf_count + 1;
        }
        if s[i] == 'F' && s[i+1] == 'S' {
            fs_count := fs_count + 1;
        }
        i := i + 1;
    }
    
    count_sf_equivalence(s, 0);
    count_fs_equivalence(s, 0);
    
    if sf_count > fs_count {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>
