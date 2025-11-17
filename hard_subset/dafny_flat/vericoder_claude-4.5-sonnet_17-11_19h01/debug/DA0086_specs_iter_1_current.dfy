// <vc-preamble>
predicate ValidInput(cards: seq<int>)
{
    |cards| == 5 && forall i :: 0 <= i < |cards| ==> cards[i] > 0
}

function minPossibleSum(cards: seq<int>): int
    requires ValidInput(cards)
    ensures minPossibleSum(cards) >= 0
    ensures minPossibleSum(cards) <= sum(cards)
{
    minPossibleSumUpToIndex(cards, 5)
}
// </vc-preamble>

// <vc-helpers>
function sum(cards: seq<int>): int
{
    if |cards| == 0 then 0 else cards[0] + sum(cards[1..])
}

function minPossibleSumUpToIndex(cards: seq<int>, n: int): int
    requires ValidInput(cards)
    requires 0 <= n <= 5
    ensures minPossibleSumUpToIndex(cards, n) >= 0
    decreases n
{
    if n == 0 then 0
    else if n == 1 then cards[0]
    else
        var skipCurrent := minPossibleSumUpToIndex(cards, n - 1);
        var takeCurrent := cards[n - 1] + (if n >= 2 then minPossibleSumUpToIndex(cards, n - 2) else 0);
        if skipCurrent < takeCurrent then skipCurrent else takeCurrent
}

function computeMinSum(cards: seq<int>, n: int, memo: seq<int>): (int, seq<int>)
    requires ValidInput(cards)
    requires 0 <= n <= 5
    requires |memo| == 6
    decreases n
{
    if n == 0 then (0, memo[n := 0])
    else if n == 1 then (cards[0], memo[n := cards[0]])
    else
        var (skipVal, memo1) := computeMinSum(cards, n - 1, memo);
        var (prevVal, memo2) := if n >= 2 then computeMinSum(cards, n - 2, memo1) else (0, memo1);
        var takeCurrent := cards[n - 1] + prevVal;
        var minVal := if skipVal < takeCurrent then skipVal else takeCurrent;
        (minVal, memo2[n := minVal])
}
// </vc-helpers>

// <vc-spec>
method solve(cards: seq<int>) returns (result: int)
    requires ValidInput(cards)
    ensures result >= 0
    ensures result <= sum(cards)
    ensures result == minPossibleSum(cards)
// </vc-spec>
// <vc-code>
{
    var dp := new int[6];
    dp[0] := 0;
    dp[1] := cards[0];
    
    var i := 2;
    while i <= 5
        invariant 2 <= i <= 6
        invariant dp[0] == 0
        invariant dp[1] == cards[0]
    {
        var skipCurrent := dp[i - 1];
        var takeCurrent := cards[i - 1] + dp[i - 2];
        if skipCurrent < takeCurrent {
            dp[i] := skipCurrent;
        } else {
            dp[i] := takeCurrent;
        }
        i := i + 1;
    }
    
    result := dp[5];
}
// </vc-code>
