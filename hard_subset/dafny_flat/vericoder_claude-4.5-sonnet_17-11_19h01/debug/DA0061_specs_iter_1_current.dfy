// <vc-preamble>
function count_occurrences(s: seq<nat>, value: nat): nat
{
    if |s| == 0 then 0
    else if s[0] == value then 1 + count_occurrences(s[1..], value)
    else count_occurrences(s[1..], value)
}

function sum_seq(s: seq<nat>): nat
{
    if |s| == 0 then 0
    else s[0] + sum_seq(s[1..])
}

predicate subarray_matches_desired(subarray: seq<nat>, desired: seq<nat>, m: nat)
    requires |desired| == m
{
    forall color :: 1 <= color <= m ==> count_occurrences(subarray, color) == desired[color-1]
}

predicate ValidInput(n: nat, m: nat, colors: seq<nat>, desired: seq<nat>)
{
    |colors| == n &&
    |desired| == m &&
    (forall i :: 0 <= i < |colors| ==> 1 <= colors[i] <= m) &&
    (forall i :: 0 <= i < |desired| ==> desired[i] >= 0) &&
    sum_seq(desired) <= n
}
// </vc-preamble>

// <vc-helpers>
predicate subarray_matches(colors: seq<nat>, i: nat, j: nat, desired: seq<nat>, m: nat)
    requires i <= j < |colors|
    requires |desired| == m
{
    subarray_matches_desired(colors[i..j+1], desired, m)
}

function count_occurrences_range(s: seq<nat>, value: nat, start: nat, end_: nat): nat
    requires 0 <= start <= end_ <= |s|
    decreases end_ - start
{
    if start == end_ then 0
    else if s[start] == value then 1 + count_occurrences_range(s, value, start+1, end_)
    else count_occurrences_range(s, value, start+1, end_)
}

lemma count_occurrences_range_equiv(s: seq<nat>, value: nat, i: nat, j: nat)
    requires 0 <= i <= j < |s|
    ensures count_occurrences_range(s, value, i, j+1) == count_occurrences(s[i..j+1], value)
{
    if i == j {
        assert s[i..j+1] == [s[i]];
    } else {
        count_occurrences_range_equiv(s, value, i+1, j);
        assert s[i..j+1] == [s[i]] + s[i+1..j+1];
    }
}

method check_subarray(colors: seq<nat>, i: nat, j: nat, desired: seq<nat>, m: nat) returns (matches: bool)
    requires 0 <= i <= j < |colors|
    requires |desired| == m
    requires forall k :: 0 <= k < |colors| ==> 1 <= colors[k] <= m
    ensures matches <==> subarray_matches_desired(colors[i..j+1], desired, m)
{
    matches := true;
    var color := 1;
    while color <= m
        invariant 1 <= color <= m + 1
        invariant matches ==> forall c :: 1 <= c < color ==> count_occurrences(colors[i..j+1], c) == desired[c-1]
    {
        var cnt := count_occurrences_range(colors, color, i, j);
        count_occurrences_range_equiv(colors, color, i, j);
        if cnt != desired[color-1] {
            matches := false;
        }
        color := color + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, colors: seq<nat>, desired: seq<nat>) returns (result: string)
    requires ValidInput(n, m, colors, desired)
    ensures result == "YES" <==> exists i, j :: 0 <= i <= j < n && subarray_matches_desired(colors[i..j+1], desired, m)
    ensures result == "YES" || result == "NO"
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall ii, jj :: 0 <= ii <= jj < i && jj < n ==> !subarray_matches_desired(colors[ii..jj+1], desired, m)
    {
        var j := i;
        while j < n
            invariant i <= j <= n
            invariant forall jj :: i <= jj < j && jj < n ==> !subarray_matches_desired(colors[i..jj+1], desired, m)
        {
            var matches := check_subarray(colors, i, j, desired, m);
            if matches {
                result := "YES";
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    result := "NO";
}
// </vc-code>
