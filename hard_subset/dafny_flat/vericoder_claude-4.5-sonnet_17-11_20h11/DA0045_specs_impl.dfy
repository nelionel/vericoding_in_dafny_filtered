// <vc-preamble>
function NormalizeAngle(angle: int): int
{
    var n := angle % 360;
    if n < 0 then n + 360 else n
}

function DeviationFromVertical(angle: int): int
    requires 0 <= angle < 360
{
    if angle <= 180 then angle else 360 - angle
}

function ImageAngleAfterRotations(cameraAngle: int, rotations: int): int
    requires 0 <= rotations <= 3
{
    NormalizeAngle(-cameraAngle + 90 * rotations)
}

function ImageDeviationAfterRotations(cameraAngle: int, rotations: int): int
    requires 0 <= rotations <= 3
{
    DeviationFromVertical(ImageAngleAfterRotations(cameraAngle, rotations))
}

predicate IsOptimalRotations(cameraAngle: int, result: int)
    requires 0 <= result <= 3
{
    forall k :: 0 <= k <= 3 ==> 
        var result_deviation := ImageDeviationAfterRotations(cameraAngle, result);
        var k_deviation := ImageDeviationAfterRotations(cameraAngle, k);
        result_deviation < k_deviation || (result_deviation == k_deviation && result <= k)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): strengthened lemma to prove optimal rotation exists and matches the computed result */
lemma OptimalRotationsExists(cameraAngle: int, candidate: int)
    requires 0 <= candidate <= 3
    requires forall r :: 0 <= r <= 3 ==> 
        ImageDeviationAfterRotations(cameraAngle, candidate) < ImageDeviationAfterRotations(cameraAngle, r) ||
        (ImageDeviationAfterRotations(cameraAngle, candidate) == ImageDeviationAfterRotations(cameraAngle, r) && candidate <= r)
    ensures IsOptimalRotations(cameraAngle, candidate)
{
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
    ensures 0 <= result <= 3
    ensures IsOptimalRotations(x, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): compute optimal rotation and invoke lemma to prove postcondition */
{
    var dev0 := ImageDeviationAfterRotations(x, 0);
    var dev1 := ImageDeviationAfterRotations(x, 1);
    var dev2 := ImageDeviationAfterRotations(x, 2);
    var dev3 := ImageDeviationAfterRotations(x, 3);
    
    result := 0;
    var minDev := dev0;
    
    if dev1 < minDev || (dev1 == minDev && 1 < result) {
        result := 1;
        minDev := dev1;
    }
    
    if dev2 < minDev || (dev2 == minDev && 2 < result) {
        result := 2;
        minDev := dev2;
    }
    
    if dev3 < minDev || (dev3 == minDev && 3 < result) {
        result := 3;
        minDev := dev3;
    }
    
    assert minDev == ImageDeviationAfterRotations(x, result);
    assert forall r :: 0 <= r <= 3 ==> minDev <= ImageDeviationAfterRotations(x, r);
    assert forall r :: 0 <= r <= 3 ==> 
        ImageDeviationAfterRotations(x, result) < ImageDeviationAfterRotations(x, r) ||
        (ImageDeviationAfterRotations(x, result) == ImageDeviationAfterRotations(x, r) && result <= r);
    OptimalRotationsExists(x, result);
}
// </vc-code>
