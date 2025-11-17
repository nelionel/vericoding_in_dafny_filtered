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
        var prev := minPossibleSumUpToIndex(cards, n - 1);
        var includeCurrent := prev + cards[n - 1];
        var skipCurrent := prev;
        if includeCurrent < skipCurrent then includeCurrent else skipCurrent
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
  result := minPossibleSumUpToIndex(cards, 5);
}
// </vc-code>
