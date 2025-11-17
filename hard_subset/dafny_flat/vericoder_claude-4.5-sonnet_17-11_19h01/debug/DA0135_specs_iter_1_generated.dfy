// <vc-preamble>
predicate ValidInput(s: string)
{
    |s| >= 0 && forall i :: 0 <= i < |s| ==> s[i] in {'A', 'B', 'C', '.'}
}

predicate HasAllThreeColors(s: string, start: int)
    requires 0 <= start <= |s| - 3
{
    'A' in s[start..start+3] && 'B' in s[start..start+3] && 'C' in s[start..start+3]
}

predicate PossibleToGetAllColors(s: string)
{
    |s| >= 3 && exists i :: 0 <= i <= |s| - 3 && HasAllThreeColors(s, i)
}
// </vc-preamble>

// <vc-helpers>
function CountInWindow(s: string, start: int, c: char): int
    requires 0 <= start <= |s|
    requires start + 3 <= |s|
{
    (if start < |s| && s[start] == c then 1 else 0) +
    (if start + 1 < |s| && s[start + 1] == c then 1 else 0) +
    (if start + 2 < |s| && s[start + 2] == c then 1 else 0)
}

lemma WindowContainsChar(s: string, start: int, c: char)
    requires 0 <= start <= |s| - 3
    requires c in s[start..start+3]
    ensures exists j :: start <= j < start + 3 && j < |s| && s[j] == c
{
    var sub := s[start..start+3];
    assert sub == [s[start], s[start+1], s[start+2]];
    if s[start] == c {
        assert s[start] == c;
    } else if s[start+1] == c {
        assert s[start+1] == c;
    } else {
        assert s[start+2] == c;
    }
}

lemma CheckWindowForAllColors(s: string, i: int)
    requires 0 <= i <= |s| - 3
    ensures HasAllThreeColors(s, i) <==> 
        ('A' in s[i..i+3] && 'B' in s[i..i+3] && 'C' in s[i..i+3])
{
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures result == "Yes" ==> PossibleToGetAllColors(s)
    ensures result == "No" ==> !PossibleToGetAllColors(s)
    ensures result == "Yes" || result == "No"
// </vc-spec>
// <vc-code>
{
    if |s| < 3 {
        result := "No";
        return;
    }
    
    var i := 0;
    while i <= |s| - 3
        invariant 0 <= i <= |s| - 3 + 1
        invariant forall j :: 0 <= j < i ==> !HasAllThreeColors(s, j)
    {
        var hasA := s[i] == 'A' || s[i+1] == 'A' || s[i+2] == 'A';
        var hasB := s[i] == 'B' || s[i+1] == 'B' || s[i+2] == 'B';
        var hasC := s[i] == 'C' || s[i+1] == 'C' || s[i+2] == 'C';
        
        if hasA && hasB && hasC {
            assert 'A' in s[i..i+3];
            assert 'B' in s[i..i+3];
            assert 'C' in s[i..i+3];
            assert HasAllThreeColors(s, i);
            result := "Yes";
            return;
        }
        
        i := i + 1;
    }
    
    assert forall j :: 0 <= j <= |s| - 3 ==> !HasAllThreeColors(s, j);
    result := "No";
}
// </vc-code>
