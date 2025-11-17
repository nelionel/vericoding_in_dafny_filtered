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
/* helper modified by LLM (iteration 3): fixed postconditions to match seq_min definition */
function FindFirstMin(arr: seq<int>, minVal: int, start: int): int
    requires |arr| > 0
    requires 0 <= start < |arr|
    requires minVal == seq_min(arr)
    requires exists k :: start <= k < |arr| && arr[k] == minVal
    decreases |arr| - start
    ensures 0 <= FindFirstMin(arr, minVal, start) < |arr|
    ensures arr[FindFirstMin(arr, minVal, start)] == minVal
    ensures forall k :: start <= k < FindFirstMin(arr, minVal, start) ==> arr[k] != minVal
{
    if arr[start] == minVal then start
    else FindFirstMin(arr, minVal, start + 1)
}

function FindLastMin(arr: seq<int>, minVal: int, end: int): int
    requires |arr| > 0
    requires 0 <= end < |arr|
    requires minVal == seq_min(arr)
    requires exists k :: 0 <= k <= end && arr[k] == minVal
    decreases end
    ensures 0 <= FindLastMin(arr, minVal, end) < |arr|
    ensures arr[FindLastMin(arr, minVal, end)] == minVal
    ensures forall k :: FindLastMin(arr, minVal, end) < k <= end ==> arr[k] != minVal
{
    if arr[end] == minVal then end
    else FindLastMin(arr, minVal, end - 1)
}

lemma MinExistsInRange(arr: seq<int>)
    requires |arr| > 0
    ensures exists i :: 0 <= i < |arr| && arr[i] == seq_min(arr)
{
}

lemma TwoMinsExist(arr: seq<int>)
    requires ValidInput(arr)
    ensures exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr)
{
}

lemma MinExistsFromStart(arr: seq<int>, start: int)
    requires |arr| > 0
    requires 0 <= start < |arr|
    ensures exists k :: start <= k < |arr| && arr[k] == seq_min(arr)
{
    assert seq_min(arr) in arr;
    var minVal := seq_min(arr);
    assert exists i :: 0 <= i < |arr| && arr[i] == minVal;
}

lemma MinExistsToEnd(arr: seq<int>, end: int)
    requires |arr| > 0
    requires 0 <= end < |arr|
    ensures exists k :: 0 <= k <= end && arr[k] == seq_min(arr)
{
    assert seq_min(arr) in arr;
    var minVal := seq_min(arr);
    assert exists i :: 0 <= i < |arr| && arr[i] == minVal;
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
/* code modified by LLM (iteration 3): strengthened proof with explicit bounds reasoning */
{
    var minVal := seq_min(arr);
    
    MinExistsFromStart(arr, 0);
    var firstIdx := FindFirstMin(arr, minVal, 0);
    
    MinExistsToEnd(arr, |arr| - 1);
    var lastIdx := FindLastMin(arr, minVal, |arr| - 1);
    
    assert arr[firstIdx] == minVal;
    assert arr[lastIdx] == minVal;
    assert forall k :: 0 <= k < firstIdx ==> arr[k] != minVal;
    assert forall k :: lastIdx < k < |arr| ==> arr[k] != minVal;
    
    TwoMinsExist(arr);
    assert firstIdx < lastIdx;
    
    result := lastIdx - firstIdx;
    
    assert arr[firstIdx] == arr[lastIdx] == minVal;
    assert result > 0;
    assert result <= |arr| - 1;
    
    forall i, j | 0 <= i < j < |arr| && arr[i] == arr[j] == minVal
        ensures j - i >= result
    {
        assert forall k :: 0 <= k < firstIdx ==> arr[k] != minVal;
        assert forall k :: lastIdx < k < |arr| ==> arr[k] != minVal;
        if i < firstIdx {
            assert arr[i] == minVal;
            assert false;
        }
        if j > lastIdx {
            assert arr[j] == minVal;
            assert false;
        }
        assert i >= firstIdx;
        assert j <= lastIdx;
        assert j - i >= lastIdx - firstIdx;
    }
}
// </vc-code>
