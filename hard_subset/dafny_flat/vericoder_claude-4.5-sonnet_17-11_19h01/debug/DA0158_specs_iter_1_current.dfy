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
    result := [];
    return;
  }

  var groups: seq<seq<char>> := [];
  var current_group: seq<char> := [];
  var seen_chars: set<char> := {};
  var i := 0;

  while i < |q|
    invariant 0 <= i <= |q|
    invariant |groups| <= k
    invariant |current_group| >= 0
    invariant forall j :: 0 <= j < |groups| ==> |groups[j]| > 0
    invariant forall m, n :: 0 <= m < n < |groups| ==> groups[m][0] != groups[n][0]
    invariant forall j :: 0 <= j < |groups| ==> groups[j][0] in seen_chars
    invariant |current_group| > 0 ==> current_group[0] in seen_chars
    invariant forall j :: 0 <= j < |groups| ==> forall idx :: 0 <= idx < |groups[j]| ==> groups[j][idx] == groups[j][0]
    invariant forall idx :: 0 <= idx < |current_group| ==> current_group[idx] == current_group[0]
    invariant concat_seqs(groups) + current_group == q[..i]
  {
    var c := q[i];

    if |current_group| == 0 {
      if c in seen_chars {
        result := [];
        return;
      }
      current_group := [c];
      seen_chars := seen_chars + {c};
    } else {
      if c == current_group[0] {
        current_group := current_group + [c];
      } else {
        groups := groups + [current_group];
        if |groups| >= k {
          result := [];
          return;
        }
        if c in seen_chars {
          result := [];
          return;
        }
        current_group := [c];
        seen_chars := seen_chars + {c};
      }
    }
    i := i + 1;
  }

  if |current_group| > 0 {
    groups := groups + [current_group];
  }

  if |groups| == k {
    result := groups;
  } else {
    result := [];
  }
}
// </vc-code>
