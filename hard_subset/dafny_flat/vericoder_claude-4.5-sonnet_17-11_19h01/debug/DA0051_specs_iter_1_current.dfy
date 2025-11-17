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
lemma MaxJoyExists(C: int, Hr: int, Hb: int, Wr: int, Wb: int)
  requires ValidInput(C, Hr, Hb, Wr, Wb)
  ensures exists redCount: int, blueCount: int :: 
    ValidCandyCombination(redCount, blueCount, C, Wr, Wb)
{
  assert ValidCandyCombination(0, 0, C, Wr, Wb);
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
{
  var maxJoy := 0;
  var maxRed := C / Wr;
  var r := 0;
  
  while r <= maxRed
    invariant 0 <= r <= maxRed + 1
    invariant exists redCount: int, blueCount: int :: 
      ValidCandyCombination(redCount, blueCount, C, Wr, Wb) &&
      maxJoy == Joy(redCount, blueCount, Hr, Hb)
    invariant forall redCount: int, blueCount: int ::
      ValidCandyCombination(redCount, blueCount, C, Wr, Wb) && redCount < r =>
      Joy(redCount, blueCount, Hr, Hb) <= maxJoy
  {
    var remainingC := C - r * Wr;
    var maxBlue := remainingC / Wb;
    var b := 0;
    
    while b <= maxBlue
      invariant 0 <= b <= maxBlue + 1
      invariant exists redCount: int, blueCount: int :: 
        ValidCandyCombination(redCount, blueCount, C, Wr, Wb) &&
        maxJoy == Joy(redCount, blueCount, Hr, Hb)
      invariant forall redCount: int, blueCount: int ::
        ValidCandyCombination(redCount, blueCount, C, Wr, Wb) && redCount < r =>
        Joy(redCount, blueCount, Hr, Hb) <= maxJoy
      invariant forall blueCount: int ::
        ValidCandyCombination(r, blueCount, C, Wr, Wb) && blueCount < b =>
        Joy(r, blueCount, Hr, Hb) <= maxJoy
    {
      var currentJoy := Joy(r, b, Hr, Hb);
      if currentJoy > maxJoy {
        maxJoy := currentJoy;
      }
      b := b + 1;
    }
    r := r + 1;
  }
  
  result := maxJoy;
}
// </vc-code>
