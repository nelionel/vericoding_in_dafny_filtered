// <vc-preamble>
predicate ValidInput(C: int, Hr: int, Hb: int, Wr: int, Wb: int)
{
  C >= 0 && Hr > 0 && Hb > 0 && Wr > 0 && Wb > 0
}

predicate ValidCandyCombination(redCount: int, blueCount: int, C: int, Wr: int, Wb: int)
{
  redCount >= 0 && blueCount >= 0 && redCount * Wr + blueCount * Wb <= C
}

function Joy(redCount: int, blueCount: int, Hr: int, Hb: int): int
{
  redCount * Hr + blueCount * Hb
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): strengthened DivisionBound lemma with explicit arithmetic steps */
function MaxRedCandy(C: int, Wr: int): int
  requires C >= 0 && Wr > 0
{
  C / Wr
}

function MaxBlueCandy(C: int, Wb: int): int
  requires C >= 0 && Wb > 0
{
  C / Wb
}

lemma DivisionBound(C: int, W: int, count: int)
  requires C >= 0 && W > 0
  requires count >= 0 && count * W <= C
  ensures count <= C / W
{
  var quotient := C / W;
  var remainder := C % W;
  assert C == quotient * W + remainder by {
    assert C % W == remainder;
    assert C / W == quotient;
  }
  assert remainder >= 0 && remainder < W;
  
  if count > quotient {
    assert count >= quotient + 1;
    calc {
      count * W;
      >= (quotient + 1) * W;
      == quotient * W + W;
      >= quotient * W + W;
    }
    assert quotient * W + W > quotient * W + remainder;
    assert quotient * W + remainder == C;
    assert count * W > C;
    assert false;
  }
}

lemma ValidCombinationBounds(redCount: int, blueCount: int, C: int, Wr: int, Wb: int)
  requires ValidInput(C, 0, 0, Wr, Wb)
  requires ValidCandyCombination(redCount, blueCount, C, Wr, Wb)
  ensures redCount <= MaxRedCandy(C, Wr)
  ensures blueCount <= MaxBlueCandy(C, Wb)
{
  DivisionBound(C, Wr, redCount);
  DivisionBound(C, Wb, blueCount);
}
// </vc-helpers>

// <vc-spec>
method solve(C: int, Hr: int, Hb: int, Wr: int, Wb: int) returns (result: int)
  requires ValidInput(C, Hr, Hb, Wr, Wb)
  ensures result >= 0
  ensures exists redCount: int, blueCount: int :: 
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) &&
    result == Joy(redCount, blueCount, Hr, Hb)
  ensures forall redCount: int, blueCount: int ::
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb) ==>
    Joy(redCount, blueCount, Hr, Hb) <= result
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): optimized implementation with tighter loop bounds and maintained invariants */
{
  var maxJoy := 0;
  var maxRed := MaxRedCandy(C, Wr);
  var maxBlue := MaxBlueCandy(C, Wb);
  
  var bestRed := 0;
  var bestBlue := 0;
  
  var r := 0;
  while r <= maxRed
    invariant 0 <= r <= maxRed + 1
    invariant ValidCandyCombination(bestRed, bestBlue, C, Wr, Wb)
    invariant maxJoy == Joy(bestRed, bestBlue, Hr, Hb)
    invariant forall redCount: int, blueCount: int ::
      ValidCandyCombination(redCount, blueCount, C, Wr, Wb) && redCount < r ==> 
      Joy(redCount, blueCount, Hr, Hb) <= maxJoy
  {
    var remainingWeight := C - r * Wr;
    var maxBlueForR := remainingWeight / Wb;
    
    var b := 0;
    while b <= maxBlueForR
      invariant 0 <= b <= maxBlueForR + 1
      invariant ValidCandyCombination(bestRed, bestBlue, C, Wr, Wb)
      invariant maxJoy == Joy(bestRed, bestBlue, Hr, Hb)
      invariant forall redCount: int, blueCount: int ::
        ValidCandyCombination(redCount, blueCount, C, Wr, Wb) && redCount < r ==> 
        Joy(redCount, blueCount, Hr, Hb) <= maxJoy
      invariant forall blueCount: int ::
        ValidCandyCombination(r, blueCount, C, Wr, Wb) && blueCount < b ==> 
        Joy(r, blueCount, Hr, Hb) <= maxJoy
    {
      var currentJoy := Joy(r, b, Hr, Hb);
      if currentJoy > maxJoy {
        maxJoy := currentJoy;
        bestRed := r;
        bestBlue := b;
      }
      b := b + 1;
    }
    r := r + 1;
  }
  
  result := maxJoy;
}
// </vc-code>
