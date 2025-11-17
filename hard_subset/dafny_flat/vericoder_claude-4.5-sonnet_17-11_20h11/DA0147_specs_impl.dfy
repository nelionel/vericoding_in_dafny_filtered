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
/* helper modified by LLM (iteration 3): Fixed RemoveOne to use witness syntax and added proofs for multiset lemmas */
ghost predicate IsSubset(s1: multiset<int>, s2: multiset<int>)
{
  forall x :: s1[x] <= s2[x]
}

function FindIndex(s: seq<int>, x: int): int
  requires x in s
  ensures 0 <= FindIndex(s, x) < |s|
  ensures s[FindIndex(s, x)] == x
{
  if s[0] == x then 0 else 1 + FindIndex(s[1..], x)
}

function RemoveOne(s: seq<int>, x: int): seq<int>
  requires x in s
  ensures |RemoveOne(s, x)| == |s| - 1
  ensures multiset(s) == multiset([x]) + multiset(RemoveOne(s, x))
{
  var i := FindIndex(s, x);
  s[..i] + s[i+1..]
}

function RemoveFromSeq(s: seq<int>, a: int, b: int, c: int): seq<int>
  requires a in s
  requires b in s
  requires c in s
  requires a != b && b != c && a != c
  ensures multiset(s) == multiset([a, b, c]) + multiset(RemoveFromSeq(s, a, b, c))
{
  var s1 := RemoveOne(s, a);
  assert b in s && a in s && a != b;
  assert multiset(s) == multiset([a]) + multiset(s1);
  assert b in multiset(s1);
  assert b in s1;
  var s2 := RemoveOne(s1, b);
  assert c in s && c != a && c != b;
  assert c in multiset(s1);
  assert c in s1;
  assert c in multiset(s2);
  assert c in s2;
  var s3 := RemoveOne(s2, c);
  s3
}

lemma FlattenAppendLemma(result: seq<seq<int>>, triplet: seq<int>)
  ensures FlattenPartition(result + [triplet]) == FlattenPartition(result) + triplet
{
  if |result| == 0 {
    assert result + [triplet] == [triplet];
  } else {
    calc {
      FlattenPartition(result + [triplet]);
      result[0] + FlattenPartition((result + [triplet])[1..]);
      result[0] + FlattenPartition(result[1..] + [triplet]);
      { FlattenAppendLemma(result[1..], triplet); }
      result[0] + FlattenPartition(result[1..]) + triplet;
      FlattenPartition(result) + triplet;
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
/* code modified by LLM (iteration 3): Added assertions to prove triplet elements are distinct and in remaining */
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
    var ti := 0;
    var tj := 0;
    var tk := 0;
    
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
            ti := i; tj := j; tk := k;
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
    
    assert |triplet| == 3;
    assert triplet[0] == remaining[ti];
    assert triplet[1] == remaining[tj];
    assert triplet[2] == remaining[tk];
    assert ti < tj < tk;
    assert triplet[0] in remaining;
    assert triplet[1] in remaining;
    assert triplet[2] in remaining;
    assert triplet[0] != triplet[1] && triplet[1] != triplet[2] && triplet[0] != triplet[2];
    
    var old_remaining := remaining;
    remaining := RemoveFromSeq(remaining, triplet[0], triplet[1], triplet[2]);
    
    assert multiset(old_remaining) == multiset(triplet) + multiset(remaining);
    FlattenAppendLemma(result, triplet);
    
    result := result + [triplet];
    count := count + 1;
  }
}
// </vc-code>
