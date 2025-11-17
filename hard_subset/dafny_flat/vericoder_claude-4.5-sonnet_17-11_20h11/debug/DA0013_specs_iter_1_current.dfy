// <vc-preamble>
function seq_min(s: seq<int>): int
    requires |s| > 0
    ensures seq_min(s) in s
    ensures forall k :: 0 <= k < |s| ==> seq_min(s) <= s[k]
{
    if |s| == 1 then s[0]
    else if s[0] <= seq_min(s[1..]) then s[0]
    else seq_min(s[1..])
}

predicate ValidInput(arr: seq<int>)
{
    |arr| >= 2 && 
    exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr)
}
// </vc-preamble>

// <vc-helpers>
predicate IsMinIndex(arr: seq<int>, idx: int)
{
    0 <= idx < |arr| && arr[idx] == seq_min(arr)
}

lemma MinIndexExists(arr: seq<int>)
    requires |arr| > 0
    ensures exists i :: IsMinIndex(arr, i)
{
    var m := seq_min(arr);
    assert m in arr;
}

function FindFirstMinIndex(arr: seq<int>, start: int): int
    requires |arr| > 0
    requires 0 <= start < |arr|
    requires exists i :: start <= i < |arr| && arr[i] == seq_min(arr)
    ensures start <= FindFirstMinIndex(arr, start) < |arr|
    ensures arr[FindFirstMinIndex(arr, start)] == seq_min(arr)
    ensures forall k :: start <= k < FindFirstMinIndex(arr, start) ==> arr[k] != seq_min(arr)
    decreases |arr| - start
{
    if arr[start] == seq_min(arr) then start
    else FindFirstMinIndex(arr, start + 1)
}

function FindLastMinIndex(arr: seq<int>, end: int): int
    requires |arr| > 0
    requires 0 <= end < |arr|
    requires exists i :: 0 <= i <= end && arr[i] == seq_min(arr)
    ensures 0 <= FindLastMinIndex(arr, end) <= end
    ensures arr[FindLastMinIndex(arr, end)] == seq_min(arr)
    ensures forall k :: FindLastMinIndex(arr, end) < k <= end ==> arr[k] != seq_min(arr)
    decreases end
{
    if arr[end] == seq_min(arr) then end
    else FindLastMinIndex(arr, end - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<int>) returns (result: int)
    requires ValidInput(arr)
    ensures result > 0
    ensures result <= |arr| - 1
    ensures exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr) && j - i == result
    ensures forall i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr) ==> j - i >= result
// </vc-spec>
// <vc-code>
{
    MinIndexExists(arr);
    var firstMin := FindFirstMinIndex(arr, 0);
    var lastMin := FindLastMinIndex(arr, |arr| - 1);
    result := lastMin - firstMin;
}
// </vc-code>
