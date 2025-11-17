// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0 && '\n' in input
}

predicate CanBeConstructedByOperations(input: string)
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    if |lines| < 2 then false
    else
        var firstLine := lines[0];
        var gridLines := lines[1..];
        var dimensions := ParseDimensions(firstLine);
        var n := dimensions.0;
        var m := dimensions.1;
        if n <= 0 || m <= 0 || |gridLines| != n then false
        else if !ValidGrid(gridLines, m) then false
        else
            (forall col {:trigger} :: 0 <= col < m ==>
                var rowsWithThisCol := set i | 0 <= i < n && col < |gridLines[i]| && gridLines[i][col] == '#';
                |rowsWithThisCol| <= 1 ||
                (forall i, j :: i in rowsWithThisCol && j in rowsWithThisCol ==>
                    GetRowPattern(gridLines[i], m) == GetRowPattern(gridLines[j], m)))
}

predicate ValidGrid(gridLines: seq<string>, m: int)
{
    (forall i :: 0 <= i < |gridLines| ==> |gridLines[i]| == m) &&
    (forall i :: 0 <= i < |gridLines| ==> 
        forall j :: 0 <= j < |gridLines[i]| ==> gridLines[i][j] in {'.', '#'})
}

function GetRowPattern(row: string, m: int): set<int>
    requires |row| == m
{
    set j | 0 <= j < m && row[j] == '#'
}

function SplitLines(input: string): seq<string>
    requires |input| > 0
{
    SplitLinesHelper(input, 0, [])
}

function ParseDimensions(line: string): (int, int)
{
    var parts := SplitOnSpace(line);
    if |parts| >= 2 then
        (StringToInt(parts[0]), StringToInt(parts[1]))
    else
        (0, 0)
}
// </vc-preamble>

// <vc-helpers>
function SplitLinesHelper(input: string, start: int, acc: seq<string>): seq<string>
    requires |input| > 0
    decreases |input| - start
{
    if start >= |input| then acc
    else
        var nextNewline := FindNextNewline(input, start);
        if nextNewline == -1 then
            acc + [input[start..]]
        else
            SplitLinesHelper(input, nextNewline + 1, acc + [input[start..nextNewline]])
}

function FindNextNewline(input: string, start: int): int
    requires |input| > 0
    decreases |input| - start
{
    if start >= |input| then -1
    else if input[start] == '\n' then start
    else FindNextNewline(input, start + 1)
}

function SplitOnSpace(line: string): seq<string>
{
    SplitOnSpaceHelper(line, 0, [])
}

function SplitOnSpaceHelper(line: string, start: int, acc: seq<string>): seq<string>
    decreases |line| - start
{
    if start >= |line| then acc
    else
        var nextSpace := FindNextSpace(line, start);
        if nextSpace == -1 then
            acc + [line[start..]]
        else if nextSpace == start then
            SplitOnSpaceHelper(line, start + 1, acc)
        else
            SplitOnSpaceHelper(line, nextSpace + 1, acc + [line[start..nextSpace]])
}

function FindNextSpace(line: string, start: int): int
    decreases |line| - start
{
    if start >= |line| then -1
    else if line[start] == ' ' then start
    else FindNextSpace(line, start + 1)
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' && |s| > 1 then -StringToIntHelper(s[1..], 0)
    else StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, acc: int): int
    decreases |s|
{
    if |s| == 0 then acc
    else if '0' <= s[0] <= '9' then
        StringToIntHelper(s[1..], acc * 10 + (s[0] as int - '0' as int))
    else
        acc
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures result == "Yes\n" || result == "No\n"
    ensures |result| > 0
    ensures result == "Yes\n" <==> CanBeConstructedByOperations(stdin_input)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(stdin_input);
    if |lines| < 2 {
        result := "No\n";
        return;
    }
    var firstLine := lines[0];
    var gridLines := lines[1..];
    var dimensions := ParseDimensions(firstLine);
    var n := dimensions.0;
    var m := dimensions.1;
    if n <= 0 || m <= 0 || |gridLines| != n {
        result := "No\n";
        return;
    }
    if !ValidGrid(gridLines, m) {
        result := "No\n";
        return;
    }
    var col := 0;
    while col < m
    {
        var rowsWithThisCol := set i | 0 <= i < n && col < |gridLines[i]| && gridLines[i][col] == '#';
        if |rowsWithThisCol| > 1 {
            var valid := true;
            var i := 0;
            while i < n && valid
            {
                if i in rowsWithThisCol {
                    var j := 0;
                    while j < n && valid
                    {
                        if j in rowsWithThisCol {
                            var pattern_i := GetRowPattern(gridLines[i], m);
                            var pattern_j := GetRowPattern(gridLines[j], m);
                            if pattern_i != pattern_j {
                                valid := false;
                            }
                        }
                        j := j + 1;
                    }
                }
                i := i + 1;
            }
            if !valid {
                result := "No\n";
                return;
            }
        }
        col := col + 1;
    }
    result := "Yes\n";
}
// </vc-code>
