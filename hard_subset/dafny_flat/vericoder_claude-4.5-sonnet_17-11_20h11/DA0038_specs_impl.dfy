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
/* helper modified by LLM (iteration 3): Added helper to find G position */
function FindG(s: string): int
    requires exists i :: 0 <= i < |s| && s[i] == 'G'
{
    if s[0] == 'G' then 0
    else FindG(s[1..]) + 1
}

/* helper modified by LLM (iteration 3): Added helper to find T position */
function FindT(s: string): int
    requires exists i :: 0 <= i < |s| && s[i] == 'T'
{
    if s[0] == 'T' then 0
    else FindT(s[1..]) + 1
}

/* helper modified by LLM (iteration 3): Helper to check if path from start to target is clear */
predicate PathClear(s: string, start: int, target: int, k: int)
    requires 0 <= start < |s|
    requires 0 <= target < |s|
    requires k > 0
{
    start < target &&
    (target - start) % k == 0 &&
    (forall pos :: start < pos < target && (pos - start) % k == 0 ==> 0 <= pos < |s| && s[pos] !in {'G', 'T', '#'})
}

/* helper modified by LLM (iteration 3): Lemma to prove CanReachTarget when path is clear */
lemma PathClearImpliesCanReach(s: string, gPos: int, tPos: int, k: int)
    requires k > 0
    requires 0 <= gPos < |s|
    requires 0 <= tPos < |s|
    requires s[gPos] == 'G'
    requires s[tPos] == 'T'
    requires forall j :: 0 <= j < gPos ==> s[j] !in {'G', 'T'}
    requires PathClear(s, gPos, tPos, k)
    ensures CanReachTarget(s, k)
{
}

/* helper modified by LLM (iteration 3): Lemma to prove !CanReachTarget when path is blocked */
lemma NoPathImpliesNotCanReach(s: string, gPos: int, tPos: int, k: int)
    requires k > 0
    requires 0 <= gPos < |s|
    requires 0 <= tPos < |s|
    requires s[gPos] == 'G'
    requires s[tPos] == 'T'
    requires forall j :: 0 <= j < gPos ==> s[j] !in {'G', 'T'}
    requires !PathClear(s, gPos, tPos, k)
    ensures !CanReachTarget(s, k)
{
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
    /* code modified by LLM (iteration 3): Fixed loop invariants and bounds checking */
    var gPos := FindG(s);
    var tPos := FindT(s);
    
    if gPos > tPos {
        NoPathImpliesNotCanReach(s, gPos, tPos, k);
        result := "NO";
        return;
    }
    
    if (tPos - gPos) % k != 0 {
        NoPathImpliesNotCanReach(s, gPos, tPos, k);
        result := "NO";
        return;
    }
    
    var current := gPos;
    var canReach := true;
    
    while current < tPos
        invariant gPos <= current <= tPos
        invariant (current - gPos) % k == 0
        invariant canReach ==> (forall pos :: gPos < pos < current && (pos - gPos) % k == 0 ==> s[pos] !in {'G', 'T', '#'})
        decreases tPos - current
    {
        var next := current + k;
        
        if next > tPos {
            canReach := false;
            break;
        }
        
        if next == tPos {
            current := next;
            break;
        }
        
        assert next < tPos;
        assert next < |s|;
        
        if s[next] == '#' || s[next] == 'G' || s[next] == 'T' {
            canReach := false;
            break;
        }
        
        current := next;
    }
    
    if canReach && current == tPos {
        PathClearImpliesCanReach(s, gPos, tPos, k);
        result := "YES";
    } else {
        NoPathImpliesNotCanReach(s, gPos, tPos, k);
        result := "NO";
    }
}
// </vc-code>
