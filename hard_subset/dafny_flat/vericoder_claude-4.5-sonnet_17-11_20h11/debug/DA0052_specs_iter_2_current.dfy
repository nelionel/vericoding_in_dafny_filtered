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
/* helper modified by LLM (iteration 2): added lemmas to prove recursive equivalence */
function CountDIterative(s: string, i: int): int
  requires 0 <= i <= |s|
  requires forall j :: 0 <= j < |s| ==> s[j] == 'D' || s[j] == 'R'
  ensures CountDIterative(s, i) >= 0
  ensures CountDIterative(s, i) <= i
{
  if i == 0 then 0
  else (if s[i-1] == 'D' then 1 else 0) + CountDIterative(s, i-1)
}

function CountRIterative(s: string, i: int): int
  requires 0 <= i <= |s|
  requires forall j :: 0 <= j < |s| ==> s[j] == 'D' || s[j] == 'R'
  ensures CountRIterative(s, i) >= 0
  ensures CountRIterative(s, i) <= i
{
  if i == 0 then 0
  else (if s[i-1] == 'R' then 1 else 0) + CountRIterative(s, i-1)
}

lemma CountDIterativeCorrect(s: string, i: int)
  requires 0 <= i <= |s|
  requires forall j :: 0 <= j < |s| ==> s[j] == 'D' || s[j] == 'R'
  ensures CountDIterative(s, i) == CountD(s[..i])
{
  if i == 0 {
    assert s[..0] == [];
  } else {
    CountDIterativeCorrect(s, i-1);
    assert s[..i] == s[..i-1] + [s[i-1]];
    calc {
      CountD(s[..i]);
      ==
      CountD(s[..i-1] + [s[i-1]]);
      ==
      (if s[i-1] == 'D' then 1 else 0) + CountD(s[..i-1]);
      ==
      (if s[i-1] == 'D' then 1 else 0) + CountDIterative(s, i-1);
      ==
      CountDIterative(s, i);
    }
  }
}

lemma CountRIterativeCorrect(s: string, i: int)
  requires 0 <= i <= |s|
  requires forall j :: 0 <= j < |s| ==> s[j] == 'D' || s[j] == 'R'
  ensures CountRIterative(s, i) == CountR(s[..i])
{
  if i == 0 {
    assert s[..0] == [];
  } else {
    CountRIterativeCorrect(s, i-1);
    assert s[..i] == s[..i-1] + [s[i-1]];
    calc {
      CountR(s[..i]);
      ==
      CountR(s[..i-1] + [s[i-1]]);
      ==
      (if s[i-1] == 'R' then 1 else 0) + CountR(s[..i-1]);
      ==
      (if s[i-1] == 'R' then 1 else 0) + CountRIterative(s, i-1);
      ==
      CountRIterative(s, i);
    }
  }
}

lemma CountDConcatenation(s1: string, s2: string)
  requires forall j :: 0 <= j < |s1| ==> s1[j] == 'D' || s1[j] == 'R'
  requires forall j :: 0 <= j < |s2| ==> s2[j] == 'D' || s2[j] == 'R'
  ensures CountD(s1 + s2) == CountD(s1) + CountD(s2)
{
  if |s2| == 0 {
    assert s1 + s2 == s1;
  } else {
    CountDConcatenation(s1, s2[1..]);
    assert (s1 + s2)[1..] == s1 + s2[1..];
  }
}

lemma CountRConcatenation(s1: string, s2: string)
  requires forall j :: 0 <= j < |s1| ==> s1[j] == 'D' || s1[j] == 'R'
  requires forall j :: 0 <= j < |s2| ==> s2[j] == 'D' || s2[j] == 'R'
  ensures CountR(s1 + s2) == CountR(s1) + CountR(s2)
{
  if |s2| == 0 {
    assert s1 + s2 == s1;
  } else {
    CountRConcatenation(s1, s2[1..]);
    assert (s1 + s2)[1..] == s1 + s2[1..];
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
/* code modified by LLM (iteration 2): invoke concatenation lemmas to prove postconditions */
{
  var countD := 0;
  var countR := 0;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant countD == CountDIterative(s, i)
    invariant countR == CountRIterative(s, i)
  {
    if s[i] == 'D' {
      countD := countD + 1;
    } else {
      countR := countR + 1;
    }
    i := i + 1;
  }
  
  CountDIterativeCorrect(s, n);
  CountRIterativeCorrect(s, n);
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
