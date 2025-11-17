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
/* helper modified by LLM (iteration 2): added lemmas to prove IsSorted and multiset properties for InsertSorted and SortSeq */
predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma InsertSortedPreservesOrder(x: int, s: seq<int>, i: int, j: int)
  requires IsSorted(s)
  requires 0 <= i < j < |InsertSorted(x, s)|
  ensures InsertSorted(x, s)[i] <= InsertSorted(x, s)[j]
{
  if |s| == 0 {
  } else if x <= s[0] {
  } else {
    var result := [s[0]] + InsertSorted(x, s[1..]);
    if i == 0 && j > 0 {
      if j == 1 {
      } else {
        InsertSortedPreservesOrder(x, s[1..], 0, j - 2);
      }
    } else if i > 0 && j > 0 {
      InsertSortedPreservesOrder(x, s[1..], i - 1, j - 1);
    }
  }
}

function InsertSorted(x: int, s: seq<int>): seq<int>
  requires IsSorted(s)
  ensures IsSorted(InsertSorted(x, s))
  ensures multiset(InsertSorted(x, s)) == multiset(s) + multiset{x}
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else 
    var result := [s[0]] + InsertSorted(x, s[1..]);
    assert forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j] by {
      forall i, j | 0 <= i < j < |result| ensures result[i] <= result[j] {
        InsertSortedPreservesOrder(x, s[1..], i - 1, j - 1);
      }
    }
    result
}

function SortSeq(s: seq<int>): seq<int>
  ensures IsSorted(SortSeq(s))
  ensures multiset(SortSeq(s)) == multiset(s)
{
  if |s| == 0 then []
  else 
    var tail := SortSeq(s[1..]);
    var result := InsertSorted(s[0], tail);
    assert multiset(result) == multiset(tail) + multiset{s[0]};
    assert multiset(tail) == multiset(s[1..]);
    assert multiset(s) == multiset{s[0]} + multiset(s[1..]);
    result
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

lemma MultisetSliceAppend(s: seq<int>, i: int, j: int)
  requires 0 <= i <= j <= |s|
  ensures multiset(s[..j]) == multiset(s[..i]) + multiset(s[i..j])
{
  if i == j {
    assert s[i..j] == [];
    assert s[..j] == s[..i];
  } else {
    assert s[..j] == s[..j-1] + [s[j-1]];
    if i < j - 1 {
      MultisetSliceAppend(s, i, j - 1);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, numbers: seq<int>) returns (result: seq<seq<int>>)
    requires ValidInput(n, numbers)
    ensures NoPartitionExists(result) || ValidPartition(result, numbers)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added MultisetSliceAppend lemma call to prove multiset property */
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
      MultisetSliceAppend(sorted, i, i + 3);
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
