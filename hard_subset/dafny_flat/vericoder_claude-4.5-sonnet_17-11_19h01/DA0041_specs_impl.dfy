// <vc-preamble>
predicate ContainsLowercase(s: string)
{
    exists i :: 0 <= i < |s| && 'a' <= s[i] <= 'z'
}

predicate ContainsUppercase(s: string)
{
    exists i :: 0 <= i < |s| && 'A' <= s[i] <= 'Z'
}

predicate ContainsDigit(s: string)
{
    exists i :: 0 <= i < |s| && '0' <= s[i] <= '9'
}

predicate IsValidPassword(s: string)
{
    |s| >= 5 && ContainsLowercase(s) && ContainsUppercase(s) && ContainsDigit(s)
}

function TrimNewline(s: string): string
{
    if |s| > 0 && s[|s|-1] == '\n' then s[..|s|-1] else s
}

function StripWhitespace(s: string): string
    decreases |s|
{
    if |s| == 0 then s
    else if s[0] == ' ' || s[0] == '\t' || s[0] == '\n' || s[0] == '\r' then
        StripWhitespace(s[1..])
    else if s[|s|-1] == ' ' || s[|s|-1] == '\t' || s[|s|-1] == '\n' || s[|s|-1] == '\r' then
        StripWhitespace(s[..|s|-1])
    else s
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added lemmas to establish Contains* predicates from witness indices */
lemma LowerExistsLemma(s: string, idx: int)
  requires 0 <= idx < |s|
  requires 'a' <= s[idx] <= 'z'
  ensures ContainsLowercase(s)
{
}

lemma UpperExistsLemma(s: string, idx: int)
  requires 0 <= idx < |s|
  requires 'A' <= s[idx] <= 'Z'
  ensures ContainsUppercase(s)
{
}

lemma DigitExistsLemma(s: string, idx: int)
  requires 0 <= idx < |s|
  requires '0' <= s[idx] <= '9'
  ensures ContainsDigit(s)
{
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures var processedInput := TrimNewline(input);
            var stripped := StripWhitespace(processedInput);
            if IsValidPassword(stripped) then
                output == "Correct\n"
            else
                output == "Too weak\n"
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Invoke lemmas before checking validity to establish postcondition */
  var processedInput := TrimNewline(input);
  var stripped := StripWhitespace(processedInput);
  
  if |stripped| >= 5 {
    var hasLower := false;
    var hasUpper := false;
    var hasDigit := false;
    var lowerIdx: int := -1;
    var upperIdx: int := -1;
    var digitIdx: int := -1;
    
    var i := 0;
    while i < |stripped|
      invariant 0 <= i <= |stripped|
      invariant hasLower ==> 0 <= lowerIdx < i && 'a' <= stripped[lowerIdx] <= 'z'
      invariant hasUpper ==> 0 <= upperIdx < i && 'A' <= stripped[upperIdx] <= 'Z'
      invariant hasDigit ==> 0 <= digitIdx < i && '0' <= stripped[digitIdx] <= '9'
    {
      if 'a' <= stripped[i] <= 'z' {
        hasLower := true;
        lowerIdx := i;
      }
      if 'A' <= stripped[i] <= 'Z' {
        hasUpper := true;
        upperIdx := i;
      }
      if '0' <= stripped[i] <= '9' {
        hasDigit := true;
        digitIdx := i;
      }
      i := i + 1;
    }
    
    if hasLower && hasUpper && hasDigit {
      LowerExistsLemma(stripped, lowerIdx);
      UpperExistsLemma(stripped, upperIdx);
      DigitExistsLemma(stripped, digitIdx);
      assert ContainsLowercase(stripped);
      assert ContainsUppercase(stripped);
      assert ContainsDigit(stripped);
      assert IsValidPassword(stripped);
      output := "Correct\n";
    } else {
      output := "Too weak\n";
    }
  } else {
    output := "Too weak\n";
  }
}
// </vc-code>
