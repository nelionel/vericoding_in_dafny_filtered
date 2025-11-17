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
lemma CountOccurrencesConcat(s1: seq<nat>, s2: seq<nat>, value: nat)
    ensures count_occurrences(s1 + s2, value) == count_occurrences(s1, value) + count_occurrences(s2, value)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        calc {
            count_occurrences(s1 + s2, value);
            ==
            if (s1 + s2)[0] == value then 1 + count_occurrences((s1 + s2)[1..], value) else count_occurrences((s1 + s2)[1..], value);
            ==
            if s1[0] == value then 1 + count_occurrences(s1[1..] + s2, value) else count_occurrences(s1[1..] + s2, value);
            == { CountOccurrencesConcat(s1[1..], s2, value); }
            if s1[0] == value then 1 + count_occurrences(s1[1..], value) + count_occurrences(s2, value) else count_occurrences(s1[1..], value) + count_occurrences(s2, value);
            ==
            count_occurrences(s1, value) + count_occurrences(s2, value);
        }
    }
}

lemma CountOccurrencesSlice(s: seq<nat>, i: int, j: int, value: nat)
    requires 0 <= i <= j < |s|
    ensures count_occurrences(s[i..j+1], value) <= count_occurrences(s, value)
{
}

function method count_in_range(s: seq<nat>, start: int, end: int, value: nat): nat
    requires 0 <= start <= end < |s|
{
    count_occurrences(s[start..end+1], value)
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
        invariant forall i', j' :: 0 <= i' < i && i' <= j' < n ==> !subarray_matches_desired(colors[i'..j'+1], desired, m)
    {
        var j := i;
        while j < n
            invariant i <= j <= n
            invariant forall j' :: i <= j' < j ==> !subarray_matches_desired(colors[i..j'+1], desired, m)
        {
            var subarray := colors[i..j+1];
            var matches := true;
            var color := 1;
            while color <= m
                invariant 1 <= color <= m + 1
                invariant matches ==> forall c :: 1 <= c < color ==> count_occurrences(subarray, c) == desired[c-1]
            {
                if count_occurrences(subarray, color) != desired[color-1] {
                    matches := false;
                }
                color := color + 1;
            }
            if matches {
                assert subarray_matches_desired(subarray, desired, m);
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
