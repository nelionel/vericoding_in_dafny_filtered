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
/* helper modified by LLM (iteration 2): added precondition k > 1 to SumProperty call */
lemma SumProperty(s: seq<int>, x: int)
    requires |s| > 0
    ensures sum(s + [x]) == sum(s) + x
{
    if |s| == 1 {
        calc {
            sum(s + [x]);
            == s[0] + sum((s + [x])[1..]);
            == s[0] + sum([x]);
            == s[0] + x + sum([]);
            == s[0] + x;
            == sum(s) + x;
        }
    } else {
        calc {
            sum(s + [x]);
            == s[0] + sum((s + [x])[1..]);
            == { assert (s + [x])[1..] == s[1..] + [x]; }
               s[0] + sum(s[1..] + [x]);
            == { SumProperty(s[1..], x); }
               s[0] + sum(s[1..]) + x;
            == sum(s) + x;
        }
    }
}

lemma SumFirstK(k: int)
    requires k > 0
    ensures k * (k + 1) / 2 == sum(seq(k, i requires 0 <= i < k => i + 1))
{
    var s := seq(k, i requires 0 <= i < k => i + 1);
    SumFirstKHelper(k, s);
}

lemma SumFirstKHelper(k: int, s: seq<int>)
    requires k > 0
    requires s == seq(k, i requires 0 <= i < k => i + 1)
    ensures sum(s) == k * (k + 1) / 2
    decreases k
{
    if k == 1 {
        calc {
            sum(s);
            == sum([1]);
            == 1;
            == 1 * 2 / 2;
        }
    } else {
        var s' := seq(k - 1, i requires 0 <= i < k - 1 => i + 1);
        SumFirstKHelper(k - 1, s');
        assert s == s' + [k];
        SumProperty(s', k);
        calc {
            sum(s);
            == sum(s' + [k]);
            == sum(s') + k;
            == (k - 1) * k / 2 + k;
            == ((k - 1) * k + 2 * k) / 2;
            == k * (k + 1) / 2;
        }
    }
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
    /* code modified by LLM (iteration 2): handle k=1 case separately to avoid empty sequence in SumProperty call */
    var minSum := k * (k + 1) / 2;
    
    if minSum > n {
        result := [-1];
        return;
    }
    
    var base := seq(k, i requires 0 <= i < k => i + 1);
    SumFirstK(k);
    assert sum(base) == minSum;
    
    var remainder := n - minSum;
    
    if k == 1 {
        result := [1 + remainder];
        assert |result| == k;
        assert sum(result) == 1 + remainder;
        assert sum(result) == minSum + remainder;
        assert sum(result) == n;
    } else {
        result := base[..k-1] + [base[k-1] + remainder];
        
        assert |result| == k;
        assert result[k-1] == k + remainder;
        assert |base[..k-1]| > 0;
        
        SumProperty(base[..k-1], k + remainder);
        assert sum(result) == sum(base[..k-1]) + (k + remainder);
        
        assert base[..k-1] == seq(k-1, i requires 0 <= i < k-1 => i + 1);
        SumFirstK(k-1);
        assert sum(base[..k-1]) == (k-1) * k / 2;
        
        calc {
            sum(result);
            == sum(base[..k-1]) + (k + remainder);
            == (k-1) * k / 2 + k + remainder;
            == (k-1) * k / 2 + k + (n - minSum);
            == (k-1) * k / 2 + k + (n - k * (k + 1) / 2);
            == n;
        }
    }
}
// </vc-code>
