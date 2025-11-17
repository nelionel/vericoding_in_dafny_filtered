// <vc-preamble>
function CountDistinct(s: string): int
{
    |set c | 0 <= c < |s| :: s[c]|
}

predicate ValidInput(input: string)
{
    |input| > 0 &&
    input[|input|-1] == '\n' &&
    |input| >= 2 &&
    forall i :: 0 <= i < |input|-1 ==> 'a' <= input[i] <= 'z'
}

predicate CorrectOutput(username: string, output: string)
{
    var distinctCount := CountDistinct(username);
    (distinctCount % 2 == 1 ==> output == "IGNORE HIM!\n") &&
    (distinctCount % 2 == 0 ==> output == "CHAT WITH HER!\n")
}
// </vc-preamble>

// <vc-helpers>
function CountDistinctChars(s: string, pos: int): set<char>
  requires 0 <= pos <= |s|
  decreases pos
{
  if pos == 0 then {} else CountDistinctChars(s, pos - 1) + {s[pos - 1]}
}

lemma CountDistinctCorrect(s: string)
  ensures CountDistinct(s) == |CountDistinctChars(s, |s|)|
{
  CountDistinctHelper(s, |s|);
}

lemma CountDistinctHelper(s: string, pos: int)
  requires 0 <= pos <= |s|
  ensures |set c | 0 <= c < pos :: s[c]| == |CountDistinctChars(s, pos)|
  decreases pos
{
  if pos == 0 {
    assert set c | 0 <= c < 0 :: s[c] == {};
  } else {
    CountDistinctHelper(s, pos - 1);
    var prevSet := set c | 0 <= c < pos - 1 :: s[c];
    var currSet := set c | 0 <= c < pos :: s[c];
    assert currSet == prevSet + {s[pos - 1]};
  }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures var username := input[..|input|-1];
            CorrectOutput(username, output)
// </vc-spec>
// <vc-code>
{
  var username := input[..|input|-1];
  CountDistinctCorrect(username);
  var distinctChars := CountDistinctChars(username, |username|);
  var distinctCount := |distinctChars|;
  
  if distinctCount % 2 == 1 {
    output := "IGNORE HIM!\n";
  } else {
    output := "CHAT WITH HER!\n";
  }
}
// </vc-code>
