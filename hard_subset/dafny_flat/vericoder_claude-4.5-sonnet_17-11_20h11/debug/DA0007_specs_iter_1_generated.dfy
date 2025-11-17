// <vc-preamble>
predicate ValidInput(n: int, k: int)
{
    n > 0 && k > 0
}

predicate IsStrictlyIncreasing(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i+1]
}

predicate AllPositive(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] > 0
}

function sum(s: seq<int>): int
    decreases |s|
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidSequence(s: seq<int>, n: int, k: int)
{
    |s| == k && AllPositive(s) && IsStrictlyIncreasing(s) && sum(s) == n
}

predicate IsPossible(n: int, k: int)
{
    k * (k + 1) / 2 <= n
}
// </vc-preamble>

// <vc-helpers>
lemma SumProperty(s: seq<int>, i: int, val: int)
    requires 0 <= i < |s|
    ensures sum(s[i := val]) == sum(s) - s[i] + val
{
    if i == 0 {
        assert s[i := val] == [val] + s[1..];
    } else {
        SumProperty(s[1..], i - 1, val);
    }
}

lemma SumIncreasing(k: int)
    requires k > 0
    ensures sum(seq(k, i => i + 1)) == k * (k + 1) / 2
{
    if k == 1 {
        assert seq(1, i => i + 1) == [1];
    } else {
        var s := seq(k, i => i + 1);
        var s' := seq(k - 1, i => i + 1);
        assert s == s' + [k];
        assert sum(s) == sum(s') + k;
        SumIncreasing(k - 1);
    }
}

lemma MinSumLemma(k: int)
    requires k > 0
    ensures k * (k + 1) / 2 == sum(seq(k, i => i + 1))
{
    SumIncreasing(k);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures (|result| == 1 && result[0] == -1) || 
            (ValidSequence(result, n, k))
    ensures (|result| == 1 && result[0] == -1) <==> !IsPossible(n, k)
// </vc-spec>
// <vc-code>
{
    var minSum := k * (k + 1) / 2;
    
    if minSum > n {
        result := [-1];
        return;
    }
    
    result := seq(k, i => i + 1);
    var remaining := n - minSum;
    
    MinSumLemma(k);
    
    result := result[k - 1 := k + remaining];
    
    SumProperty(seq(k, i => i + 1), k - 1, k + remaining);
}
// </vc-code>
