// <vc-preamble>
predicate ValidInput(n: int, numbers: seq<int>)
{
    n >= 3 && n % 3 == 0 &&
    |numbers| == n &&
    forall i :: 0 <= i < |numbers| ==> 1 <= numbers[i] <= 7
}

predicate ValidTriplet(triplet: seq<int>)
{
    |triplet| == 3 &&
    triplet[0] < triplet[1] < triplet[2] &&
    triplet[0] > 0 && triplet[1] > 0 && triplet[2] > 0 &&
    triplet[1] % triplet[0] == 0 && triplet[2] % triplet[1] == 0
}

function FlattenPartition(result: seq<seq<int>>): seq<int>
{
    if |result| == 0 then [] else
    result[0] + FlattenPartition(result[1..])
}

predicate ValidPartition(result: seq<seq<int>>, numbers: seq<int>)
{
    |result| == |numbers| / 3 &&
    (forall i :: 0 <= i < |result| ==> ValidTriplet(result[i])) &&
    multiset(numbers) == multiset(FlattenPartition(result))
}

predicate NoPartitionExists(result: seq<seq<int>>)
{
    |result| == 0
}
// </vc-preamble>

// <vc-helpers>
predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function InsertSorted(x: int, s: seq<int>): seq<int>
  requires IsSorted(s)
  ensures IsSorted(InsertSorted(x, s))
  ensures multiset(InsertSorted(x, s)) == multiset(s) + multiset{x}
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + InsertSorted(x, s[1..])
}

function SortSeq(s: seq<int>): seq<int>
  ensures IsSorted(SortSeq(s))
  ensures multiset(SortSeq(s)) == multiset(s)
{
  if |s| == 0 then []
  else InsertSorted(s[0], SortSeq(s[1..]))
}

predicate CanFormTriplet(a: int, b: int, c: int)
{
  a > 0 && b > 0 && c > 0 &&
  a < b < c &&
  b % a == 0 && c % b == 0
}

function MakeTriplet(a: int, b: int, c: int): seq<int>
  requires a < b < c
{
  [a, b, c]
}

lemma FlattenEmpty()
  ensures FlattenPartition([]) == []
{
}

lemma FlattenSingle(t: seq<int>)
  ensures FlattenPartition([t]) == t
{
}

lemma FlattenAppend(result: seq<seq<int>>, t: seq<int>)
  ensures FlattenPartition(result + [t]) == FlattenPartition(result) + t
{
  if |result| == 0 {
    assert FlattenPartition(result + [t]) == FlattenPartition([t]);
  } else {
    assert result + [t] == [result[0]] + (result[1..] + [t]);
    FlattenAppend(result[1..], t);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, numbers: seq<int>) returns (result: seq<seq<int>>)
    requires ValidInput(n, numbers)
    ensures NoPartitionExists(result) || ValidPartition(result, numbers)
// </vc-spec>
// <vc-code>
{
  var sorted := SortSeq(numbers);
  result := [];
  var i := 0;
  
  while i + 2 < |sorted|
    invariant 0 <= i <= |sorted|
    invariant i % 3 == 0
    invariant |result| == i / 3
    invariant forall j :: 0 <= j < |result| ==> ValidTriplet(result[j])
    invariant multiset(FlattenPartition(result)) == multiset(sorted[..i])
  {
    var a := sorted[i];
    var b := sorted[i + 1];
    var c := sorted[i + 2];
    
    if a < b && b < c && b % a == 0 && c % b == 0 {
      var triplet := [a, b, c];
      assert ValidTriplet(triplet);
      
      FlattenAppend(result, triplet);
      assert multiset(FlattenPartition(result + [triplet])) == multiset(FlattenPartition(result)) + multiset(triplet);
      assert multiset(sorted[..i+3]) == multiset(sorted[..i]) + multiset(sorted[i..i+3]);
      
      result := result + [triplet];
      i := i + 3;
    } else {
      result := [];
      return;
    }
  }
  
  if i != |sorted| {
    result := [];
    return;
  }
  
  assert i == |sorted|;
  assert sorted[..i] == sorted;
  assert multiset(sorted) == multiset(numbers);
}
// </vc-code>
