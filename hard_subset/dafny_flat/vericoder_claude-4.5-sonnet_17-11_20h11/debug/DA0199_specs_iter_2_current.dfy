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
/* helper modified by LLM (iteration 2): Added lemma to prove equivalence between map-based counting and specification */
function DiagSum(pos: (int, int)): int { pos.0 + pos.1 }

function DiagDiff(pos: (int, int)): int { pos.0 - pos.1 }

function CountPairsInMap(counts: map<int, int>): int
{
  if counts == map[] then 0
  else
    var k :| k in counts.Keys;
    var c := counts[k];
    c * (c - 1) / 2 + CountPairsInMap(map key | key in counts.Keys && key != k :: counts[key])
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

lemma CountingEquivalence(positions: seq<(int, int)>, diagSumMap: map<int, int>, diagDiffMap: map<int, int>)
  requires ValidInput(positions)
  requires diagSumMap == BuildDiagSumMap(positions, |positions|)
  requires diagDiffMap == BuildDiagDiffMap(positions, |positions|)
  ensures CountPairsInMap(diagSumMap) + CountPairsInMap(diagDiffMap) == CountAttackingPairs(positions)
{
}
// </vc-helpers>

// <vc-spec>
method SolveBishops(positions: seq<(int, int)>) returns (result: int)
    requires ValidInput(positions)
    ensures ValidOutput(positions, result)
    ensures result >= 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Added invariants and lemma calls to prove correctness */
{
  var diagSumMap: map<int, int> := map[];
  var diagDiffMap: map<int, int> := map[];
  
  var i := 0;
  while i < |positions|
    invariant 0 <= i <= |positions|
    invariant diagSumMap == BuildDiagSumMap(positions, i)
    invariant diagDiffMap == BuildDiagDiffMap(positions, i)
  {
    var dSum := positions[i].0 + positions[i].1;
    var dDiff := positions[i].0 - positions[i].1;
    
    diagSumMap := diagSumMap[dSum := if dSum in diagSumMap then diagSumMap[dSum] + 1 else 1];
    diagDiffMap := diagDiffMap[dDiff := if dDiff in diagDiffMap then diagDiffMap[dDiff] + 1 else 1];
    
    i := i + 1;
  }
  
  result := 0;
  ghost var originalSumMap := diagSumMap;
  var sumKeys := diagSumMap.Keys;
  while sumKeys != {}
    decreases |sumKeys|
    invariant sumKeys <= diagSumMap.Keys
    invariant forall k :: k in sumKeys ==> k in diagSumMap
    invariant result == CountPairsInMap(map k | k in diagSumMap.Keys && k !in sumKeys :: diagSumMap[k])
  {
    var key :| key in sumKeys;
    assert key in diagSumMap;
    var count := diagSumMap[key];
    result := result + (count * (count - 1)) / 2;
    sumKeys := sumKeys - {key};
  }
  
  var sumResult := result;
  var diffKeys := diagDiffMap.Keys;
  while diffKeys != {}
    decreases |diffKeys|
    invariant diffKeys <= diagDiffMap.Keys
    invariant forall k :: k in diffKeys ==> k in diagDiffMap
    invariant result == sumResult + CountPairsInMap(map k | k in diagDiffMap.Keys && k !in diffKeys :: diagDiffMap[k])
  {
    var key :| key in diffKeys;
    assert key in diagDiffMap;
    var count := diagDiffMap[key];
    result := result + (count * (count - 1)) / 2;
    diffKeys := diffKeys - {key};
  }
  
  CountingEquivalence(positions, diagSumMap, diagDiffMap);
}
// </vc-code>
