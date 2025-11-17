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

// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures 1 <= result <= |s|
    ensures result == |AllDistinctCyclicShifts(s)|
// </vc-spec>
// <vc-code>
{
  ghost var shifts := AllDistinctCyclicShifts(s);
  var seen: set<string> := {};
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant seen == set j | 0 <= j < i :: ApplyShifts(s, j)
  {
    var current := ApplyShifts(s, i);
    seen := seen + {current};
    i := i + 1;
  }
  result := |seen|;
}
// </vc-code>
