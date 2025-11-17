// <vc-preamble>
function GenerateSquares(): seq<int>
    ensures forall i :: 0 <= i < |GenerateSquares()| ==> GenerateSquares()[i] > 0
{
    GenerateSquaresHelper(1, 44721)
}

function IsSubsequence(pattern: string, text: string): bool
{
    IsSubsequenceHelper(pattern, text, 0, 0)
}

function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else IntToStringHelper(n)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed type conversion for digit to char */
function GenerateSquaresHelper(start: int, end: int): seq<int>
    requires start > 0
    requires end >= start
    decreases end - start
{
    if start > end then []
    else [start * start] + GenerateSquaresHelper(start + 1, end)
}

function IsSubsequenceHelper(pattern: string, text: string, pIdx: int, tIdx: int): bool
    requires 0 <= pIdx <= |pattern|
    requires 0 <= tIdx <= |text|
    decreases |pattern| - pIdx, |text| - tIdx
{
    if pIdx == |pattern| then true
    else if tIdx == |text| then false
    else if pattern[pIdx] == text[tIdx] then
        IsSubsequenceHelper(pattern, text, pIdx + 1, tIdx + 1)
    else
        IsSubsequenceHelper(pattern, text, pIdx, tIdx + 1)
}

function IntToStringHelper(n: int): string
    requires n > 0
    decreases n
{
    if n < 10 then [(n + '0' as int) as char]
    else IntToStringHelper(n / 10) + [((n % 10) + '0' as int) as char]
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires s[0] != '0' || |s| == 1
    ensures result == -1 || result >= 0
    ensures result == -1 ==> forall sq :: sq in GenerateSquares() ==> !IsSubsequence(IntToString(sq), s)
    ensures result >= 0 ==> exists sq :: sq in GenerateSquares() && IsSubsequence(IntToString(sq), s) && result == |s| - |IntToString(sq)|
    ensures result >= 0 ==> forall sq :: sq in GenerateSquares() && IsSubsequence(IntToString(sq), s) ==> |s| - |IntToString(sq)| >= result
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed implementation with proper loop invariants */
    var squares := GenerateSquares();
    var minDeletes := |s| + 1;
    var found := false;
    
    var i := 0;
    while i < |squares|
        invariant 0 <= i <= |squares|
        invariant found ==> minDeletes <= |s|
        invariant found ==> exists sq :: sq in squares && IsSubsequence(IntToString(sq), s) && |s| - |IntToString(sq)| == minDeletes
        invariant found ==> forall j :: 0 <= j < i && squares[j] in squares ==> IsSubsequence(IntToString(squares[j]), s) ==> |s| - |IntToString(squares[j])| >= minDeletes
        invariant !found ==> forall j :: 0 <= j < i && squares[j] in squares ==> !IsSubsequence(IntToString(squares[j]), s)
    {
        var sq := squares[i];
        var sqStr := IntToString(sq);
        
        if IsSubsequence(sqStr, s) {
            var deletes := |s| - |sqStr|;
            if deletes < minDeletes {
                minDeletes := deletes;
                found := true;
            }
        }
        
        i := i + 1;
    }
    
    if found {
        result := minDeletes;
    } else {
        result := -1;
    }
}
// </vc-code>
