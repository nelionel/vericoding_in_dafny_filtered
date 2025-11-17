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
/* helper modified by LLM (iteration 2): added lemmas to prove concat_seqs properties */
lemma concat_seqs_append(s1: seq<seq<char>>, s2: seq<char>)
  ensures concat_seqs(s1 + [s2]) == concat_seqs(s1) + s2
{
  if |s1| == 0 {
    assert concat_seqs(s1 + [s2]) == concat_seqs([s2]) == s2;
    assert concat_seqs(s1) + s2 == [] + s2 == s2;
  } else {
    calc {
      concat_seqs(s1 + [s2]);
      == s1[0] + concat_seqs((s1 + [s2])[1..]);
      == s1[0] + concat_seqs(s1[1..] + [s2]);
      == { concat_seqs_append(s1[1..], s2); }
      s1[0] + concat_seqs(s1[1..]) + s2;
      == concat_seqs(s1) + s2;
    }
  }
}

lemma concat_seqs_prefix(s: seq<seq<char>>, s2: seq<char>)
  ensures concat_seqs(s) + s2 == concat_seqs(s + [s2])
{
  concat_seqs_append(s, s2);
}
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
  /* code modified by LLM (iteration 2): added lemma calls and fixed invariant maintenance */
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
    invariant |current_group| > 0 ==> current_group[0] !in (set j | 0 <= j < |groups| :: groups[j][0])
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
        concat_seqs_append(groups, current_group);
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
    concat_seqs_append(groups, current_group);
    groups := groups + [current_group];
  }

  if |groups| == k {
    result := groups;
  } else {
    result := [];
  }
}
// </vc-code>
