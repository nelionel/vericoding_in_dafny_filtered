// <vc-preamble>
function CyclicShiftForward(s: string): string
    requires |s| > 0
{
    s[1..] + [s[0]]
}

predicate ValidInput(s: string)
{
    |s| > 0
}

function ApplyShifts(s: string, steps: nat): string
    requires |s| > 0
    decreases steps
{
    if steps == 0 then s
    else CyclicShiftForward(ApplyShifts(s, steps - 1))
}

function AllDistinctCyclicShifts(s: string): set<string>
    requires |s| > 0
{
    set i | 0 <= i < |s| :: ApplyShifts(s, i)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemma to prove set construction equivalence */
lemma SetConstructionEquivalence(s: string, i: int)
    requires |s| > 0
    requires 0 <= i <= |s|
    ensures (set j | 0 <= j < i :: ApplyShifts(s, j)) == if i == 0 then {} else (set j | 0 <= j < i - 1 :: ApplyShifts(s, j)) + {ApplyShifts(s, i - 1)}
{
    if i == 0 {
        assert (set j | 0 <= j < i :: ApplyShifts(s, j)) == {};
    } else {
        var prev := set j | 0 <= j < i - 1 :: ApplyShifts(s, j);
        var current := set j | 0 <= j < i :: ApplyShifts(s, j);
        assert current == prev + {ApplyShifts(s, i - 1)};
    }
}

lemma AllShiftsIncluded(s: string)
    requires |s| > 0
    ensures (set j | 0 <= j < |s| :: ApplyShifts(s, j)) == AllDistinctCyclicShifts(s)
{
    assert AllDistinctCyclicShifts(s) == set i | 0 <= i < |s| :: ApplyShifts(s, i);
}

lemma SetSizeBounds(s: string)
    requires |s| > 0
    ensures 1 <= |AllDistinctCyclicShifts(s)| <= |s|
{
    var shifts := AllDistinctCyclicShifts(s);
    assert ApplyShifts(s, 0) == s;
    assert s in shifts;
    assert |shifts| >= 1;
    assert shifts == set i | 0 <= i < |s| :: ApplyShifts(s, i);
    assert |shifts| <= |s|;
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures 1 <= result <= |s|
    ensures result == |AllDistinctCyclicShifts(s)|
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added lemma calls to help verification */
  SetSizeBounds(s);
  ghost var shifts := AllDistinctCyclicShifts(s);
  var seen: set<string> := {};
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant seen == set j | 0 <= j < i :: ApplyShifts(s, j)
  {
    SetConstructionEquivalence(s, i + 1);
    var current := ApplyShifts(s, i);
    seen := seen + {current};
    i := i + 1;
  }
  AllShiftsIncluded(s);
  result := |seen|;
}
// </vc-code>
