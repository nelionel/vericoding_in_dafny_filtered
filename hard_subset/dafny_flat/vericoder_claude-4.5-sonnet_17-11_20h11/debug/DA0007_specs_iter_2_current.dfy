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
/* helper modified by LLM (iteration 2): Fixed SumIncreasing lemma to properly prove sum property */
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
    decreases k
{
    if k == 1 {
        assert seq(1, i => i + 1) == [1];
        assert sum([1]) == 1;
        assert 1 * (1 + 1) / 2 == 1;
    } else {
        var s := seq(k, i => i + 1);
        var s' := seq(k - 1, i => i + 1);
        SumIncreasing(k - 1);
        assert forall i :: 0 <= i < k - 1 ==> s'[i] == i + 1;
        assert forall i :: 0 <= i < k - 1 ==> s[i] == s'[i];
        assert s[k - 1] == k;
        calc {
            sum(s);
            s[0] + sum(s[1..]);
            {
                assert s[1..] == s';
            }
            s[0] + sum(s');
            1 + sum(s');
            {
                SumIncreasing(k - 1);
            }
            1 + (k - 1) * k / 2;
            (2 + (k - 1) * k) / 2;
            (2 + k * k - k) / 2;
            (k * k + k) / 2;
            k * (k + 1) / 2;
        }
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
    /* code modified by LLM (iteration 2): Fixed sum calculation proof */
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
