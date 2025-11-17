// <vc-preamble>
predicate ValidInput(word: string) 
{
    1 <= |word| <= 10 && forall i :: 0 <= i < |word| ==> 'A' <= word[i] <= 'Z'
}

function Group1(): string { "AEFHIKLMNTVWXYZ" }
function Group2(): string { "BCDGJOPQRSU" }

predicate AllInGroup1(word: string)
{
    forall i :: 0 <= i < |word| ==> word[i] in Group1()
}

predicate AllInGroup2(word: string)
{
    forall i :: 0 <= i < |word| ==> word[i] in Group2()
}

predicate AllInSameGroup(word: string)
{
    AllInGroup1(word) || AllInGroup2(word)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Add lemma to prove group membership is exhaustive */
lemma GroupsExhaustive()
  ensures forall c :: 'A' <= c <= 'Z' ==> c in Group1() || c in Group2()
{
}
// </vc-helpers>

// <vc-spec>
method solve(word: string) returns (result: string)
    requires ValidInput(word)
    ensures AllInSameGroup(word) <==> result == "YES"
    ensures result == "YES" || result == "NO"
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Add invariant to track that all chars are in at least one group, and strengthen post-loop assertions */
  var i := 0;
  var allGroup1 := true;
  var allGroup2 := true;
  
  while i < |word|
    invariant 0 <= i <= |word|
    invariant allGroup1 ==> forall j :: 0 <= j < i ==> word[j] in Group1()
    invariant allGroup2 ==> forall j :: 0 <= j < i ==> word[j] in Group2()
    invariant !allGroup1 ==> exists j :: 0 <= j < i && word[j] !in Group1()
    invariant !allGroup2 ==> exists j :: 0 <= j < i && word[j] !in Group2()
  {
    if word[i] !in Group1() {
      allGroup1 := false;
    }
    if word[i] !in Group2() {
      allGroup2 := false;
    }
    i := i + 1;
  }
  
  assert i == |word|;
  
  if allGroup1 {
    assert AllInGroup1(word);
    result := "YES";
  } else if allGroup2 {
    assert AllInGroup2(word);
    result := "YES";
  } else {
    assert !AllInGroup1(word);
    assert !AllInGroup2(word);
    result := "NO";
  }
}
// </vc-code>
