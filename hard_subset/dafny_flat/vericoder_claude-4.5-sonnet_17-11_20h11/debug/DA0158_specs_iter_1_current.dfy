// <vc-preamble>
function concat_seqs(seqs: seq<seq<char>>): seq<char>
{
    if |seqs| == 0 then []
    else seqs[0] + concat_seqs(seqs[1..])
}

predicate ValidSplit(result: seq<seq<char>>, k: int, q: seq<char>)
{
    |result| == k &&
    (forall i :: 0 <= i < |result| ==> |result[i]| > 0) &&
    (forall i, j :: 0 <= i < j < |result| ==> result[i][0] != result[j][0]) &&
    concat_seqs(result) == q
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(k: int, q: seq<char>) returns (result: seq<seq<char>>)
    requires k >= 0
    requires |q| >= 0
    ensures k <= 0 || |q| == 0 ==> |result| == 0
    ensures k > 0 && |q| > 0 ==> (
        (|result| == 0) || ValidSplit(result, k, q)
    )
// </vc-spec>
// <vc-code>
{
  if k <= 0 || |q| == 0 {
    return [];
  }
  
  var groups: seq<seq<char>> := [];
  var current_group: seq<char> := [];
  var seen_chars: set<char> := {};
  
  var i := 0;
  while i < |q|
  {
    var c := q[i];
    
    if c in seen_chars {
      if |current_group| > 0 {
        groups := groups + [current_group];
        current_group := [];
      }
      current_group := [c];
    } else {
      current_group := current_group + [c];
      seen_chars := seen_chars + {c};
    }
    
    i := i + 1;
  }
  
  if |current_group| > 0 {
    groups := groups + [current_group];
  }
  
  if |groups| == k {
    return groups;
  } else {
    return [];
  }
}
// </vc-code>
