// <vc-preamble>
predicate ValidInput(n: int, s: string)
{
  1 <= n <= 200000 && |s| == n && 
  forall i :: 0 <= i < n ==> s[i] == 'D' || s[i] == 'R'
}

function CountD(s: string): int
  requires forall i :: 0 <= i < |s| ==> s[i] == 'D' || s[i] == 'R'
  ensures CountD(s) >= 0
  ensures CountD(s) <= |s|
  ensures CountD(s) == 0 <==> forall i :: 0 <= i < |s| ==> s[i] != 'D'
{
  if |s| == 0 then 0
  else (if s[0] == 'D' then 1 else 0) + CountD(s[1..])
}

function CountR(s: string): int
  requires forall i :: 0 <= i < |s| ==> s[i] == 'D' || s[i] == 'R'
  ensures CountR(s) >= 0
  ensures CountR(s) <= |s|
  ensures CountR(s) == 0 <==> forall i :: 0 <= i < |s| ==> s[i] != 'R'
{
  if |s| == 0 then 0
  else (if s[0] == 'R' then 1 else 0) + CountR(s[1..])
}

function OptimalEliminationGameWinner(s: string): string
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] == 'D' || s[i] == 'R'
  ensures OptimalEliminationGameWinner(s) == "D" || OptimalEliminationGameWinner(s) == "R"
  ensures CountD(s) == 0 ==> OptimalEliminationGameWinner(s) == "R"
  ensures CountR(s) == 0 ==> OptimalEliminationGameWinner(s) == "D"
  ensures (forall i :: 0 <= i < |s| ==> s[i] == 'D') ==> OptimalEliminationGameWinner(s) == "D"
  ensures (forall i :: 0 <= i < |s| ==> s[i] == 'R') ==> OptimalEliminationGameWinner(s) == "R"
  ensures OptimalEliminationGameWinner(s) == "D" ==> CountD(s) > 0
  ensures OptimalEliminationGameWinner(s) == "R" ==> CountR(s) > 0
{
  if CountD(s) == 0 then "R"
  else if CountR(s) == 0 then "D"
  else if CountD(s) >= CountR(s) then "D"
  else "R"
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added lemmas to prove count invariants maintained */
lemma CountDPrefix(s: string, i: int)
  requires 0 <= i < |s|
  requires forall j :: 0 <= j < |s| ==> s[j] == 'D' || s[j] == 'R'
  ensures CountD(s[..i+1]) == CountD(s[..i]) + (if s[i] == 'D' then 1 else 0)
{
  assert s[..i+1] == s[..i] + [s[i]];
  CountDAppend(s[..i], s[i]);
}

lemma CountDAppend(s: string, c: char)
  requires forall j :: 0 <= j < |s| ==> s[j] == 'D' || s[j] == 'R'
  requires c == 'D' || c == 'R'
  ensures CountD(s + [c]) == CountD(s) + (if c == 'D' then 1 else 0)
{
  if |s| == 0 {
    assert s + [c] == [c];
    assert CountD([c]) == (if c == 'D' then 1 else 0);
  } else {
    assert (s + [c])[0] == s[0];
    assert (s + [c])[1..] == s[1..] + [c];
    CountDAppend(s[1..], c);
  }
}

lemma CountRPrefix(s: string, i: int)
  requires 0 <= i < |s|
  requires forall j :: 0 <= j < |s| ==> s[j] == 'D' || s[j] == 'R'
  ensures CountR(s[..i+1]) == CountR(s[..i]) + (if s[i] == 'R' then 1 else 0)
{
  assert s[..i+1] == s[..i] + [s[i]];
  CountRAppend(s[..i], s[i]);
}

lemma CountRAppend(s: string, c: char)
  requires forall j :: 0 <= j < |s| ==> s[j] == 'D' || s[j] == 'R'
  requires c == 'D' || c == 'R'
  ensures CountR(s + [c]) == CountR(s) + (if c == 'R' then 1 else 0)
{
  if |s| == 0 {
    assert s + [c] == [c];
    assert CountR([c]) == (if c == 'R' then 1 else 0);
  } else {
    assert (s + [c])[0] == s[0];
    assert (s + [c])[1..] == s[1..] + [c];
    CountRAppend(s[1..], c);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: string)
  requires ValidInput(n, s)
  ensures result == "D" || result == "R"
  ensures result == "D" ==> CountD(s) > 0
  ensures result == "R" ==> CountR(s) > 0
  ensures CountD(s) == 0 ==> result == "R"
  ensures CountR(s) == 0 ==> result == "D"
  ensures (forall i :: 0 <= i < |s| ==> s[i] == 'D') ==> result == "D"
  ensures (forall i :: 0 <= i < |s| ==> s[i] == 'R') ==> result == "R"
  ensures result == OptimalEliminationGameWinner(s)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added lemma calls to prove invariants maintained */
{
  var countD := 0;
  var countR := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant countD == CountD(s[..i])
    invariant countR == CountR(s[..i])
  {
    CountDPrefix(s, i);
    CountRPrefix(s, i);
    if s[i] == 'D' {
      countD := countD + 1;
    } else {
      countR := countR + 1;
    }
    i := i + 1;
  }
  assert s[..n] == s;
  if countD == 0 {
    result := "R";
  } else if countR == 0 {
    result := "D";
  } else if countD >= countR {
    result := "D";
  } else {
    result := "R";
  }
}
// </vc-code>
