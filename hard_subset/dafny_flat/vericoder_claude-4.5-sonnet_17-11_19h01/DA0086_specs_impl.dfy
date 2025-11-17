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
/* helper modified by LLM (iteration 3): added lemmas to prove sum bounds and correctness of minPossibleSumUpToIndex */
function sum(cards: seq<int>): int
{
    if |cards| == 0 then 0 else cards[0] + sum(cards[1..])
}

lemma SumNonNegative(cards: seq<int>)
    requires forall i :: 0 <= i < |cards| ==> cards[i] > 0
    ensures sum(cards) >= 0
{
}

lemma SumUpToIndexBound(cards: seq<int>, n: int)
    requires ValidInput(cards)
    requires 0 <= n <= 5
    ensures minPossibleSumUpToIndex(cards, n) <= sumUpTo(cards, n)
    decreases n
{
    if n > 1 {
        SumUpToIndexBound(cards, n - 1);
        SumUpToIndexBound(cards, n - 2);
    }
}

function sumUpTo(cards: seq<int>, n: int): int
    requires 0 <= n <= |cards|
    decreases n
{
    if n == 0 then 0 else cards[n - 1] + sumUpTo(cards, n - 1)
}

lemma SumUpToLeqSum(cards: seq<int>, n: int)
    requires 0 <= n <= |cards|
    ensures sumUpTo(cards, n) <= sum(cards)
    decreases n
{
    if n > 0 {
        SumUpToLeqSum(cards, n - 1);
    }
}

function minPossibleSumUpToIndex(cards: seq<int>, n: int): int
    requires ValidInput(cards)
    requires 0 <= n <= 5
    ensures minPossibleSumUpToIndex(cards, n) >= 0
    ensures minPossibleSumUpToIndex(cards, n) <= sumUpTo(cards, n)
    decreases n
{
    SumUpToIndexBound(cards, n);
    if n == 0 then 0
    else if n == 1 then cards[0]
    else
        var skipCurrent := minPossibleSumUpToIndex(cards, n - 1);
        var takeCurrent := cards[n - 1] + minPossibleSumUpToIndex(cards, n - 2);
        if skipCurrent < takeCurrent then skipCurrent else takeCurrent
}

lemma DPCorrectness(cards: seq<int>, dp: array<int>, i: int)
    requires ValidInput(cards)
    requires dp.Length == 6
    requires 0 <= i <= 5
    requires forall j :: 0 <= j <= i ==> dp[j] == minPossibleSumUpToIndex(cards, j)
    ensures forall j :: 0 <= j <= i ==> dp[j] >= 0
    ensures forall j :: 0 <= j <= i ==> dp[j] <= sumUpTo(cards, j)
{
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
/* code modified by LLM (iteration 3): added loop invariants to prove correctness and bounds */
{
    var dp := new int[6];
    dp[0] := 0;
    dp[1] := cards[0];
    
    var i := 2;
    while i <= 5
        invariant 2 <= i <= 6
        invariant dp[0] == 0
        invariant dp[1] == cards[0]
        invariant forall j :: 0 <= j < i ==> dp[j] == minPossibleSumUpToIndex(cards, j)
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
    SumUpToLeqSum(cards, 5);
}
// </vc-code>
