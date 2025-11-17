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
/* helper modified by LLM (iteration 2): Made IsSubset ghost predicate and added compilable helper functions */
ghost predicate IsSubset(s1: multiset<int>, s2: multiset<int>)
{
  forall x :: s1[x] <= s2[x]
}

function RemoveFromSeq(s: seq<int>, a: int, b: int, c: int): seq<int>
  requires a in s
  requires b in s
  requires c in s
{
  var s1 := RemoveOne(s, a);
  var s2 := RemoveOne(s1, b);
  RemoveOne(s2, c)
}

function RemoveOne(s: seq<int>, x: int): seq<int>
  requires x in s
{
  var i :| 0 <= i < |s| && s[i] == x;
  s[..i] + s[i+1..]
}

lemma MultisetRemoveLemma(s: seq<int>, a: int, b: int, c: int)
  requires a in s
  requires b in s
  requires c in s
  requires a != b && b != c && a != c
  ensures multiset(s) == multiset([a, b, c]) + multiset(RemoveFromSeq(s, a, b, c))
{
}

lemma FlattenAppendLemma(result: seq<seq<int>>, triplet: seq<int>)
  ensures FlattenPartition(result + [triplet]) == FlattenPartition(result) + triplet
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, numbers: seq<int>) returns (result: seq<seq<int>>)
    requires ValidInput(n, numbers)
    ensures NoPartitionExists(result) || ValidPartition(result, numbers)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed to handle the case where not all triplets can be formed */
{
  result := [];
  var remaining := numbers;
  var count := 0;
  
  while count < n / 3
    invariant 0 <= count <= n / 3
    invariant |result| == count
    invariant |remaining| == n - 3 * count
    invariant forall i :: 0 <= i < |result| ==> ValidTriplet(result[i])
    invariant forall i :: 0 <= i < |remaining| ==> 1 <= remaining[i] <= 7
    invariant multiset(numbers) == multiset(FlattenPartition(result)) + multiset(remaining)
  {
    var found := false;
    var triplet: seq<int> := [];
    
    var i := 0;
    while i < |remaining| && !found
      invariant 0 <= i <= |remaining|
    {
      var j := i + 1;
      while j < |remaining| && !found
        invariant i < j <= |remaining|
      {
        var k := j + 1;
        while k < |remaining| && !found
          invariant j < k <= |remaining|
        {
          if remaining[i] < remaining[j] < remaining[k] &&
             remaining[j] % remaining[i] == 0 &&
             remaining[k] % remaining[j] == 0 {
            triplet := [remaining[i], remaining[j], remaining[k]];
            found := true;
          }
          k := k + 1;
        }
        j := j + 1;
      }
      i := i + 1;
    }
    
    if !found {
      result := [];
      return;
    }
    
    result := result + [triplet];
    remaining := RemoveFromSeq(remaining, triplet[0], triplet[1], triplet[2]);
    count := count + 1;
  }
}
// </vc-code>
