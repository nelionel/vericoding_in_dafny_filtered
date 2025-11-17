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
/* helper modified by LLM (iteration 2): strengthened lemma to prove that minimum deviation implies optimality */
lemma OptimalRotationExists(cameraAngle: int)
    ensures exists r :: 0 <= r <= 3 && IsOptimalRotations(cameraAngle, r)
{
    var dev0 := ImageDeviationAfterRotations(cameraAngle, 0);
    var dev1 := ImageDeviationAfterRotations(cameraAngle, 1);
    var dev2 := ImageDeviationAfterRotations(cameraAngle, 2);
    var dev3 := ImageDeviationAfterRotations(cameraAngle, 3);
    
    var r := if dev0 <= dev1 && dev0 <= dev2 && dev0 <= dev3 then 0
             else if dev1 <= dev0 && dev1 <= dev2 && dev1 <= dev3 then 1
             else if dev2 <= dev0 && dev2 <= dev1 && dev2 <= dev3 then 2
             else 3;
    
    assert 0 <= r <= 3;
    assert forall k :: 0 <= k <= 3 ==> ImageDeviationAfterRotations(cameraAngle, r) <= ImageDeviationAfterRotations(cameraAngle, k);
    MinDeviationIsOptimal(cameraAngle, r);
    assert IsOptimalRotations(cameraAngle, r);
}

lemma MinDeviationIsOptimal(cameraAngle: int, r: int)
    requires 0 <= r <= 3
    requires forall k :: 0 <= k <= 3 ==> ImageDeviationAfterRotations(cameraAngle, r) <= ImageDeviationAfterRotations(cameraAngle, k)
    ensures IsOptimalRotations(cameraAngle, r)
{
    assert forall k :: 0 <= k <= 3 ==>
        var result_deviation := ImageDeviationAfterRotations(cameraAngle, r);
        var k_deviation := ImageDeviationAfterRotations(cameraAngle, k);
        result_deviation < k_deviation || (result_deviation == k_deviation && r <= k);
}
// </vc-helpers>

// <vc-spec>
method solve(x: int) returns (result: int)
    ensures 0 <= result <= 3
    ensures IsOptimalRotations(x, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added explicit invariants and lemma calls to prove optimality */
{
    var dev0 := ImageDeviationAfterRotations(x, 0);
    var dev1 := ImageDeviationAfterRotations(x, 1);
    var dev2 := ImageDeviationAfterRotations(x, 2);
    var dev3 := ImageDeviationAfterRotations(x, 3);
    
    result := 0;
    var minDev := dev0;
    
    if dev1 < minDev {
        result := 1;
        minDev := dev1;
    }
    
    if dev2 < minDev {
        result := 2;
        minDev := dev2;
    }
    
    if dev3 < minDev {
        result := 3;
        minDev := dev3;
    }
    
    assert ImageDeviationAfterRotations(x, result) == minDev;
    assert forall k :: 0 <= k <= 3 ==> minDev <= ImageDeviationAfterRotations(x, k);
    MinDeviationIsOptimal(x, result);
}
// </vc-code>
