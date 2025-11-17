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
function FindG(s: string): int
    requires exists i :: 0 <= i < |s| && s[i] == 'G'
{
    if s[0] == 'G' then 0
    else FindG(s[1..]) + 1
}

function FindT(s: string): int
    requires exists i :: 0 <= i < |s| && s[i] == 'T'
{
    if s[0] == 'T' then 0
    else FindT(s[1..]) + 1
}

predicate PathClear(s: string, start: int, target: int, k: int)
    requires 0 <= start < |s|
    requires 0 <= target < |s|
    requires k > 0
{
    start < target &&
    (target - start) % k == 0 &&
    (forall pos :: start < pos < target && (pos - start) % k == 0 ==> 0 <= pos < |s| && s[pos] !in {'G', 'T', '#'})
}

function TryReach(s: string, pos: int, target: int, k: int, steps: int): bool
    requires 0 <= pos < |s|
    requires 0 <= target < |s|
    requires k > 0
    requires steps >= 0
    decreases steps
{
    if steps == 0 then
        pos == target
    else if pos + k >= |s| then
        false
    else if s[pos + k] in {'#', 'G', 'T'} then
        if s[pos + k] == 'T' && pos + k == target then true
        else false
    else
        TryReach(s, pos + k, target, k, steps - 1)
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
    var gPos := FindG(s);
    var tPos := FindT(s);
    
    if gPos > tPos {
        result := "NO";
        return;
    }
    
    var current := gPos;
    var found := false;
    
    while current < tPos
        invariant gPos <= current <= tPos
        decreases tPos - current
    {
        var next := current + k;
        if next >= |s| {
            result := "NO";
            return;
        }
        
        if next == tPos {
            found := true;
            break;
        }
        
        if s[next] == '#' || s[next] == 'G' {
            result := "NO";
            return;
        }
        
        if s[next] == 'T' {
            result := "NO";
            return;
        }
        
        current := next;
    }
    
    if found || current == tPos {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>
