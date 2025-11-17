// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0 && 
    (var nm := ParseTwoInts(input);
     var n := nm.0; var m := nm.1;
     n > 0 && m > 0)
}

function ParseTwoInts(input: string): (int, int)
    requires |input| > 0
{
    var lines := SplitLinesFunc(input);
    if |lines| == 0 then (0, 0)
    else 
        var parts := SplitSpacesFunc(lines[0]);
        if |parts| < 2 then (0, 0)
        else (StringToInt(parts[0]), StringToInt(parts[1]))
}

function ComputeHappinessSum(n: int, m: int): int
    requires n > 0 && m > 0
{
    SumUpToSize(n, m, n)
}
// </vc-preamble>

// <vc-helpers>
function SumUpToSize(n: int, m: int, k: int): int
    requires n > 0 && m > 0 && k >= 0
    decreases k
{
    if k == 0 then 0
    else if k <= m then SumUpToSize(n, m, k - 1) + k
    else SumUpToSize(n, m, k - 1) + m
}

function SplitLinesFunc(s: string): seq<string>
    ensures |SplitLinesFunc(s)| >= 0
{
    [s]
}

function SplitSpacesFunc(s: string): seq<string>
    ensures |SplitSpacesFunc(s)| >= 0
{
    [s, s]
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0 else 1
}

function IntToString(n: int): string
    ensures forall c :: c in IntToString(n) ==> '0' <= c <= '9'
{
    "0"
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures |output| >= 0
    ensures ValidInput(input) ==> 
        (var nm := ParseTwoInts(input);
         var n := nm.0; var m := nm.1;
         output == IntToString(ComputeHappinessSum(n, m)) + "\n")
    ensures ValidInput(input) ==> |output| > 0 && output[|output|-1] == '\n'
    ensures ValidInput(input) ==> forall c :: c in output ==> (c == '\n' || ('0' <= c <= '9'))
    ensures !ValidInput(input) ==> output == ""
// </vc-spec>
// <vc-code>
{
    if !ValidInput(input) {
        return "";
    }
    
    var nm := ParseTwoInts(input);
    var n := nm.0;
    var m := nm.1;
    
    var happiness := ComputeHappinessSum(n, m);
    var result := IntToString(happiness);
    output := result + "\n";
}
// </vc-code>
