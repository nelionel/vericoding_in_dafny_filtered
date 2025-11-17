// <vc-preamble>
predicate ValidInput(n: int, k: int, s: string)
{
    n >= 2 &&
    1 <= k < n &&
    |s| == n &&
    (exists i :: 0 <= i < |s| && s[i] == 'G') &&
    (exists i :: 0 <= i < |s| && s[i] == 'T') &&
    (forall i :: 0 <= i < |s| ==> s[i] in {'G', 'T', '.', '#'}) &&
    (forall i, j :: 0 <= i < j < |s| && s[i] == 'G' ==> s[j] != 'G') &&
    (forall i, j :: 0 <= i < j < |s| && s[i] == 'T' ==> s[j] != 'T')
}

function FindFirstGOrT(s: string): int
    requires exists i :: 0 <= i < |s| && s[i] in {'G', 'T'}
{
    if s[0] in {'G', 'T'} then 0
    else FindFirstGOrT(s[1..]) + 1
}

predicate CanReachTarget(s: string, k: int)
    requires k > 0
{
    exists start :: 
        0 <= start < |s| && 
        s[start] in {'G', 'T'} &&
        (forall j :: 0 <= j < start ==> s[j] !in {'G', 'T'}) &&
        (exists final :: 
            start < final < |s| &&
            s[final] in {'G', 'T'} &&
            (final - start) % k == 0 &&
            (forall pos :: start < pos < final && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
        )
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed recursive CanReachFrom predicate causing termination errors, simplified TryReach to only check path validity */
function FindG(s: string): int
    requires exists i :: 0 <= i < |s| && s[i] == 'G'
    ensures 0 <= FindG(s) < |s|
    ensures s[FindG(s)] == 'G'
    ensures forall j :: 0 <= j < FindG(s) ==> s[j] != 'G'
{
    if s[0] == 'G' then 0
    else 1 + FindG(s[1..])
}

function FindT(s: string): int
    requires exists i :: 0 <= i < |s| && s[i] == 'T'
    ensures 0 <= FindT(s) < |s|
    ensures s[FindT(s)] == 'T'
    ensures forall j :: 0 <= j < FindT(s) ==> s[j] != 'T'
{
    if s[0] == 'T' then 0
    else 1 + FindT(s[1..])
}

method TryReach(s: string, start: int, target: int, k: int) returns (canReach: bool)
    requires 0 <= start < |s|
    requires 0 <= target < |s|
    requires k > 0
    ensures canReach <==> (start <= target && (target - start) % k == 0 && (forall pos :: start < pos < target && (pos - start) % k == 0 ==> s[pos] !in {'G', 'T', '#'}))
{
    if start > target {
        return false;
    }
    if (target - start) % k != 0 {
        return false;
    }
    
    var pos := start + k;
    while pos < target
        invariant start < pos <= target
        invariant (pos - start) % k == 0
        invariant forall p :: start < p < pos && (p - start) % k == 0 ==> s[p] !in {'G', 'T', '#'}
    {
        if s[pos] == '#' || s[pos] == 'G' || s[pos] == 'T' {
            return false;
        }
        pos := pos + k;
    }
    
    return true;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, s: string) returns (result: string)
    requires ValidInput(n, k, s)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanReachTarget(s, k)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added lemma assertions to connect TryReach result with CanReachTarget definition */
    var gPos := FindG(s);
    var tPos := FindT(s);
    
    assert s[gPos] == 'G';
    assert forall j :: 0 <= j < gPos ==> s[j] != 'G';
    assert s[tPos] == 'T';
    assert forall j :: 0 <= j < tPos ==> s[j] != 'T';
    
    var canReach := TryReach(s, gPos, tPos, k);
    
    if canReach {
        assert gPos <= tPos && (tPos - gPos) % k == 0;
        assert forall pos :: gPos < pos < tPos && (pos - gPos) % k == 0 ==> s[pos] !in {'G', 'T', '#'};
        assert s[gPos] in {'G', 'T'};
        assert forall j :: 0 <= j < gPos ==> s[j] !in {'G', 'T'};
        assert gPos < tPos < |s|;
        assert s[tPos] in {'G', 'T'};
        assert (tPos - gPos) % k == 0;
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>
