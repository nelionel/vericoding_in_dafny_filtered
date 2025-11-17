// <vc-preamble>
predicate ValidInput(positions: seq<(int, int)>)
{
    |positions| >= 1 && |positions| <= 200000 &&
    (forall i :: 0 <= i < |positions| ==> 
        1 <= positions[i].0 <= 1000 && 1 <= positions[i].1 <= 1000) &&
    (forall i, j :: 0 <= i < j < |positions| ==> positions[i] != positions[j])
}

function CountAttackingPairs(positions: seq<(int, int)>): int
    requires ValidInput(positions)
{
    |set i, j | 0 <= i < j < |positions| && 
               (positions[i].0 + positions[i].1 == positions[j].0 + positions[j].1 ||
                positions[i].0 - positions[i].1 == positions[j].0 - positions[j].1) :: (i, j)|
}

predicate ValidOutput(positions: seq<(int, int)>, result: int)
    requires ValidInput(positions)
{
    result == CountAttackingPairs(positions) && result >= 0
}
// </vc-preamble>

// <vc-helpers>
function DiagSum(pos: (int, int)): int { pos.0 + pos.1 }

function DiagDiff(pos: (int, int)): int { pos.0 - pos.1 }

function CountPairsOnDiag(positions: seq<(int, int)>, diag: int, isDiagSum: bool): int
  requires ValidInput(positions)
{
  var filtered := if isDiagSum then
    seq(|positions|, i requires 0 <= i < |positions| => if DiagSum(positions[i]) == diag then 1 else 0)
  else
    seq(|positions|, i requires 0 <= i < |positions| => if DiagDiff(positions[i]) == diag then 1 else 0);
  var count := SumSeq(filtered);
  count * (count - 1) / 2
}

function SumSeq(s: seq<int>): int
{
  if |s| == 0 then 0 else s[0] + SumSeq(s[1..])
}
// </vc-helpers>

// <vc-spec>
method SolveBishops(positions: seq<(int, int)>) returns (result: int)
    requires ValidInput(positions)
    ensures ValidOutput(positions, result)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var diagSumMap: map<int, int> := map[];
  var diagDiffMap: map<int, int> := map[];
  
  var i := 0;
  while i < |positions|
  {
    var dSum := positions[i].0 + positions[i].1;
    var dDiff := positions[i].0 - positions[i].1;
    
    diagSumMap := diagSumMap[dSum := if dSum in diagSumMap then diagSumMap[dSum] + 1 else 1];
    diagDiffMap := diagDiffMap[dDiff := if dDiff in diagDiffMap then diagDiffMap[dDiff] + 1 else 1];
    
    i := i + 1;
  }
  
  result := 0;
  var sumKeys := diagSumMap.Keys;
  while sumKeys != {}
    decreases |sumKeys|
  {
    var key :| key in sumKeys;
    var count := diagSumMap[key];
    result := result + (count * (count - 1)) / 2;
    sumKeys := sumKeys - {key};
  }
  
  var diffKeys := diagDiffMap.Keys;
  while diffKeys != {}
    decreases |diffKeys|
  {
    var key :| key in diffKeys;
    var count := diagDiffMap[key];
    result := result + (count * (count - 1)) / 2;
    diffKeys := diffKeys - {key};
  }
}
// </vc-code>
