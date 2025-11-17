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
/* helper modified by LLM (iteration 3): Made CountPairsInMap iterative and added necessary lemmas */
function DiagSum(pos: (int, int)): int { pos.0 + pos.1 }

function DiagDiff(pos: (int, int)): int { pos.0 - pos.1 }

function CountPairsFromCount(c: int): int
  requires c >= 0
{
  c * (c - 1) / 2
}

function CountPairsInMap(counts: map<int, int>): int
{
  var sum := 0;
  var keys := counts.Keys;
  SumOverKeys(counts, keys)
}

function SumOverKeys(counts: map<int, int>, keys: set<int>): int
  requires keys <= counts.Keys
{
  if keys == {} then 0
  else
    var k :| k in keys;
    CountPairsFromCount(counts[k]) + SumOverKeys(counts, keys - {k})
}

function BuildDiagSumMap(positions: seq<(int, int)>, idx: int): map<int, int>
  requires ValidInput(positions)
  requires 0 <= idx <= |positions|
{
  if idx == 0 then map[]
  else
    var m := BuildDiagSumMap(positions, idx - 1);
    var key := DiagSum(positions[idx - 1]);
    m[key := if key in m then m[key] + 1 else 1]
}

function BuildDiagDiffMap(positions: seq<(int, int)>, idx: int): map<int, int>
  requires ValidInput(positions)
  requires 0 <= idx <= |positions|
{
  if idx == 0 then map[]
  else
    var m := BuildDiagDiffMap(positions, idx - 1);
    var key := DiagDiff(positions[idx - 1]);
    m[key := if key in m then m[key] + 1 else 1]
}

lemma SumOverKeysSubset(counts: map<int, int>, keys: set<int>, k: int)
  requires keys <= counts.Keys
  requires k in keys
  ensures SumOverKeys(counts, keys) == CountPairsFromCount(counts[k]) + SumOverKeys(counts, keys - {k})
{
  var k' :| k' in keys;
  if k' == k {
  } else {
    calc {
      SumOverKeys(counts, keys);
      CountPairsFromCount(counts[k']) + SumOverKeys(counts, keys - {k'});
      {
        SumOverKeysSubset(counts, keys - {k'}, k);
      }
      CountPairsFromCount(counts[k']) + CountPairsFromCount(counts[k]) + SumOverKeys(counts, keys - {k'} - {k});
      CountPairsFromCount(counts[k]) + CountPairsFromCount(counts[k']) + SumOverKeys(counts, keys - {k} - {k'});
      {
        assert keys - {k} - {k'} == keys - {k'} - {k};
        SumOverKeysSubset(counts, keys - {k}, k');
      }
      CountPairsFromCount(counts[k]) + SumOverKeys(counts, keys - {k});
    }
  }
}
// </vc-helpers>

// <vc-spec>
method SolveBishops(positions: seq<(int, int)>) returns (result: int)
    requires ValidInput(positions)
    ensures ValidOutput(positions, result)
    ensures result >= 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Simplified to direct computation without lemmas */
{
  var diagSumMap: map<int, int> := map[];
  var diagDiffMap: map<int, int> := map[];
  
  var i := 0;
  while i < |positions|
    invariant 0 <= i <= |positions|
  {
    var dSum := positions[i].0 + positions[i].1;
    var dDiff := positions[i].0 - positions[i].1;
    
    diagSumMap := diagSumMap[dSum := if dSum in diagSumMap then diagSumMap[dSum] + 1 else 1];
    diagDiffMap := diagDiffMap[dDiff := if dDiff in diagDiffMap then diagDiffMap[dDiff] + 1 else 1];
    
    i := i + 1;
  }
  
  result := 0;
  var sumKeys := diagSumMap.Keys;
  ghost var processedSum: set<int> := {};
  while sumKeys != {}
    decreases |sumKeys|
    invariant sumKeys <= diagSumMap.Keys
    invariant processedSum == diagSumMap.Keys - sumKeys
    invariant result == SumOverKeys(diagSumMap, processedSum)
  {
    var key :| key in sumKeys;
    var count := diagSumMap[key];
    result := result + (count * (count - 1)) / 2;
    sumKeys := sumKeys - {key};
    processedSum := processedSum + {key};
    SumOverKeysSubset(diagSumMap, diagSumMap.Keys - (sumKeys - {key}), key);
  }
  
  var sumResult := result;
  var diffKeys := diagDiffMap.Keys;
  ghost var processedDiff: set<int> := {};
  while diffKeys != {}
    decreases |diffKeys|
    invariant diffKeys <= diagDiffMap.Keys
    invariant processedDiff == diagDiffMap.Keys - diffKeys
    invariant result == sumResult + SumOverKeys(diagDiffMap, processedDiff)
  {
    var key :| key in diffKeys;
    var count := diagDiffMap[key];
    result := result + (count * (count - 1)) / 2;
    diffKeys := diffKeys - {key};
    processedDiff := processedDiff + {key};
    SumOverKeysSubset(diagDiffMap, diagDiffMap.Keys - (diffKeys - {key}), key);
  }
}
// </vc-code>
