// <vc-preamble>
function CountOccurrences(s: seq<int>, x: int): int
  ensures CountOccurrences(s, x) >= 0
{
  if |s| == 0 then 0
  else (if s[0] == x then 1 else 0) + CountOccurrences(s[1..], x)
}

function CountPairs(s: seq<int>): int
  ensures CountPairs(s) >= 0
{
  var positive_sessions := FilterPositive(s);
  CountPairsHelper(positive_sessions)
}

function FilterPositive(s: seq<int>): seq<int>
  ensures forall i :: 0 <= i < |FilterPositive(s)| ==> FilterPositive(s)[i] > 0
{
  if |s| == 0 then []
  else if s[0] > 0 then [s[0]] + FilterPositive(s[1..])
  else FilterPositive(s[1..])
}

function CountPairsHelper(s: seq<int>): int
  decreases |s|
  ensures CountPairsHelper(s) >= 0
{
  if |s| <= 1 then 0
  else 
    var count := CountOccurrences(s, s[0]);
    var remaining := RemoveAllOccurrences(s, s[0]);
    (if count == 2 then 1 else 0) + CountPairsHelper(remaining)
}

function RemoveAllOccurrences(s: seq<int>, x: int): seq<int>
  ensures |RemoveAllOccurrences(s, x)| <= |s|
{
  if |s| == 0 then []
  else if s[0] == x then RemoveAllOccurrences(s[1..], x)
  else [s[0]] + RemoveAllOccurrences(s[1..], x)
}

predicate ExistsIndex(s: seq<int>, x: int)
{
  exists i :: 0 <= i < |s| && s[i] == x
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed CountOccurrencesSeqComplete proof by correcting the calculation step */
lemma CountOccurrencesLemma(s: seq<int>, x: int, i: int)
  requires 0 <= i <= |s|
  ensures CountOccurrences(s, x) == CountOccurrences(s[..i], x) + CountOccurrences(s[i..], x)
  decreases i
{
  if i == 0 {
    assert s[..0] == [];
    assert s[0..] == s;
  } else {
    assert s == [s[0]] + s[1..];
    assert s[..i] == [s[0]] + s[1..i];
    CountOccurrencesLemma(s[1..], x, i - 1);
    assert s[1..][..i-1] == s[1..i];
    assert s[1..][i-1..] == s[i..];
  }
}

lemma CountOccurrencesIncremental(s: seq<int>, x: int)
  requires |s| > 0
  ensures CountOccurrences(s, x) == (if s[0] == x then 1 else 0) + CountOccurrences(s[1..], x)
{
}

function CountOccurrencesSeq(s: seq<int>, x: int, upTo: int): int
  requires 0 <= upTo <= |s|
  decreases upTo
{
  if upTo == 0 then 0
  else (if s[upTo - 1] == x then 1 else 0) + CountOccurrencesSeq(s, x, upTo - 1)
}

lemma CountOccurrencesSeqComplete(s: seq<int>, x: int)
  ensures CountOccurrencesSeq(s, x, |s|) == CountOccurrences(s, x)
  decreases |s|
{
  if |s| == 0 {
  } else {
    CountOccurrencesSeqComplete(s[..|s|-1], x);
    assert s[..|s|-1] + [s[|s|-1]] == s;
    calc {
      CountOccurrencesSeq(s, x, |s|);
      ==
      (if s[|s| - 1] == x then 1 else 0) + CountOccurrencesSeq(s, x, |s| - 1);
      ==
      (if s[|s| - 1] == x then 1 else 0) + CountOccurrences(s[..|s|-1], x);
      ==  { assert CountOccurrences(s, x) == CountOccurrences(s[..|s|-1], x) + (if s[|s|-1] == x then 1 else 0); }
      CountOccurrences(s, x);
    }
  }
}

lemma CountOccurrencesZero(s: seq<int>, x: int)
  requires !ExistsIndex(s, x)
  ensures CountOccurrences(s, x) == 0
  decreases |s|
{
  if |s| == 0 {
  } else {
    assert s[0] != x;
    CountOccurrencesZero(s[1..], x);
  }
}

lemma CountOccurrencesSeqMonotonic(s: seq<int>, x: int, i: int)
  requires 0 <= i <= |s|
  ensures CountOccurrencesSeq(s, x, i) <= CountOccurrences(s, x)
{
  CountOccurrencesSeqComplete(s, x);
  if i == |s| {
  } else {
    CountOccurrencesSeqMonotonic(s, x, i + 1);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, sessions: seq<int>) returns (result: int)
  requires n >= 1
  requires |sessions| == n
  requires forall i :: 0 <= i < |sessions| ==> sessions[i] >= 0
  ensures result == -1 || result >= 0
  ensures result == -1 ==> exists id :: id > 0 && CountOccurrences(sessions, id) > 2
  ensures result >= 0 ==> forall id :: id > 0 ==> CountOccurrences(sessions, id) <= 2
  ensures result >= 0 ==> result == CountPairs(sessions)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed invariant maintenance with helper lemmas and corrected assertions */
  var counts := map[];
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant forall id :: id in counts ==> counts[id] == CountOccurrencesSeq(sessions, id, i)
    invariant forall id :: id > 0 && ExistsIndex(sessions[..i], id) ==> id in counts
    invariant forall id :: id in counts ==> id > 0 && counts[id] <= 2
  {
    if sessions[i] > 0 {
      var id := sessions[i];
      var count := if id in counts then counts[id] else 0;
      
      if !ExistsIndex(sessions[..i], id) {
        CountOccurrencesZero(sessions[..i], id);
        assert CountOccurrencesSeq(sessions, id, i) == 0;
        assert count == 0;
      }
      
      assert sessions[..i+1] == sessions[..i] + [sessions[i]];
      assert CountOccurrencesSeq(sessions, id, i+1) == count + 1;
      
      counts := counts[id := count + 1];
      
      if counts[id] > 2 {
        CountOccurrencesSeqComplete(sessions, id);
        CountOccurrencesSeqMonotonic(sessions, id, i + 1);
        assert counts[id] <= CountOccurrences(sessions, id);
        return -1;
      }
    }
    i := i + 1;
  }
  
  assert i == n;
  assert sessions[..i] == sessions;
  
  forall id | id > 0
    ensures CountOccurrences(sessions, id) <= 2
  {
    if ExistsIndex(sessions, id) {
      CountOccurrencesSeqComplete(sessions, id);
      assert id in counts;
      assert counts[id] == CountOccurrences(sessions, id);
    } else {
      CountOccurrencesZero(sessions, id);
    }
  }
  
  result := CountPairs(sessions);
}
// </vc-code>
