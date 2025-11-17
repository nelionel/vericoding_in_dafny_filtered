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
/* helper modified by LLM (iteration 3): added ensures clauses to prove positivity and bounds */
function GenerateSquaresHelper(start: int, end: int): seq<int>
    requires start > 0
    requires end >= start
    ensures forall i :: 0 <= i < |GenerateSquaresHelper(start, end)| ==> GenerateSquaresHelper(start, end)[i] > 0
    decreases end - start
{
    if start > end then []
    else [start * start] + GenerateSquaresHelper(start + 1, end)
}

function IsSubsequenceHelper(pattern: string, text: string, pi: int, ti: int): bool
    requires 0 <= pi <= |pattern|
    requires 0 <= ti <= |text|
    decreases |pattern| - pi, |text| - ti
{
    if pi == |pattern| then true
    else if ti == |text| then false
    else if pattern[pi] == text[ti] then IsSubsequenceHelper(pattern, text, pi + 1, ti + 1)
    else IsSubsequenceHelper(pattern, text, pi, ti + 1)
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
/* code modified by LLM (iteration 3): fixed invariants to handle result >= 0 properly */
{
    var squares := GenerateSquares();
    result := -1;
    var i := 0;
    while i < |squares|
        invariant 0 <= i <= |squares|
        invariant result == -1 || result >= 0
        invariant result == -1 ==> forall j :: 0 <= j < i ==> !IsSubsequence(IntToString(squares[j]), s)
        invariant result >= 0 ==> exists j :: 0 <= j < i && IsSubsequence(IntToString(squares[j]), s) && result == |s| - |IntToString(squares[j])|
        invariant result >= 0 ==> forall j :: 0 <= j < i && IsSubsequence(IntToString(squares[j]), s) ==> |s| - |IntToString(squares[j])| >= result
    {
        var sqStr := IntToString(squares[i]);
        if IsSubsequence(sqStr, s) {
            var deletions := |s| - |sqStr|;
            if result == -1 || deletions < result {
                result := deletions;
            }
        }
        i := i + 1;
    }
}
// </vc-code>
