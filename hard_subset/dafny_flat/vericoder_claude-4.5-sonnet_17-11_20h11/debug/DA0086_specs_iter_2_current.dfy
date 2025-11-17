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
/* helper modified by LLM (iteration 2): Fixed sum function to require ValidInput and added lemmas to prove bounds */
function sum(cards: seq<int>): int
    requires ValidInput(cards)
    ensures sum(cards) >= 0
{
    if |cards| == 0 then 0
    else if |cards| == 1 then cards[0]
    else if |cards| == 2 then cards[0] + cards[1]
    else if |cards| == 3 then cards[0] + cards[1] + cards[2]
    else if |cards| == 4 then cards[0] + cards[1] + cards[2] + cards[3]
    else cards[0] + cards[1] + cards[2] + cards[3] + cards[4]
}

function minPossibleSumUpToIndex(cards: seq<int>, n: int): int
    requires ValidInput(cards)
    requires 0 <= n <= 5
    ensures minPossibleSumUpToIndex(cards, n) >= 0
    ensures minPossibleSumUpToIndex(cards, n) <= sumUpTo(cards, n)
    decreases n
{
    if n == 0 then 0
    else
        var prev := minPossibleSumUpToIndex(cards, n - 1);
        if prev < prev + cards[n - 1] then prev else prev + cards[n - 1]
}

function sumUpTo(cards: seq<int>, n: int): int
    requires ValidInput(cards)
    requires 0 <= n <= 5
    ensures sumUpTo(cards, n) >= 0
    decreases n
{
    if n == 0 then 0
    else sumUpTo(cards, n - 1) + cards[n - 1]
}

lemma SumUpToEqualsSum(cards: seq<int>)
    requires ValidInput(cards)
    ensures sumUpTo(cards, 5) == sum(cards)
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
/* code modified by LLM (iteration 2): Added lemma call to prove postcondition */
{
  SumUpToEqualsSum(cards);
  result := minPossibleSumUpToIndex(cards, 5);
}
// </vc-code>
