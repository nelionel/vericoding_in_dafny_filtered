// <vc-preamble>
datatype Wave = Wave(start_time: nat, end_time: nat, monsters: nat)

predicate ValidWaves(waves: seq<Wave>)
{
    forall i :: 0 <= i < |waves| ==> 
        waves[i].start_time <= waves[i].end_time &&
        waves[i].monsters > 0 &&
        (i > 0 ==> waves[i-1].end_time <= waves[i].start_time)
}

predicate CanSolveAllWaves(waves: seq<Wave>, k: nat)
{
    k > 0 && 
    forall i :: 0 <= i < |waves| ==> 
        CanSolveWave(waves, i, k)
}

predicate CanSolveWave(waves: seq<Wave>, waveIndex: nat, k: nat)
    requires waveIndex < |waves|
    requires k > 0
{
    var wave := waves[waveIndex];
    var timeAvailable := wave.end_time - wave.start_time + 1;
    var maxPossibleShots := timeAvailable * k;
    wave.monsters <= maxPossibleShots &&
    (waveIndex == 0 || CanReachWaveInTime(waves, waveIndex, k))
}

predicate CanReachWaveInTime(waves: seq<Wave>, waveIndex: nat, k: nat)
    requires waveIndex > 0 && waveIndex < |waves|
    requires k > 0
{
    var prevWave := waves[waveIndex - 1];
    var currWave := waves[waveIndex];
    var timeGap := currWave.start_time - prevWave.end_time;
    var reloadsNeeded := CalculateReloadsNeeded(prevWave.monsters, k);
    reloadsNeeded <= timeGap
}

function CalculateReloadsNeeded(monsters: nat, k: nat): nat
    requires k > 0
{
    if monsters <= k then 0
    else (monsters - 1) / k
}

function CalculateMinimumBullets(waves: seq<Wave>, k: nat): nat
    requires k > 0
    requires ValidWaves(waves)
    requires CanSolveAllWaves(waves, k)
    ensures |waves| > 0 ==> CalculateMinimumBullets(waves, k) > 0
{
    CalculateMinimumBulletsHelper(waves, k, 0, k)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed function name in ensures clause from 'result' to function name */
function CalculateMinimumBulletsHelper(waves: seq<Wave>, k: nat, waveIndex: nat, bulletsInChamber: nat): nat
    requires k > 0
    requires ValidWaves(waves)
    requires CanSolveAllWaves(waves, k)
    requires waveIndex <= |waves|
    requires bulletsInChamber <= k
    ensures waveIndex < |waves| ==> CalculateMinimumBulletsHelper(waves, k, waveIndex, bulletsInChamber) > 0
    decreases |waves| - waveIndex
{
    if waveIndex == |waves| then
        bulletsInChamber
    else
        var wave := waves[waveIndex];
        var shotsNeeded := wave.monsters;
        var shotsFromChamber := if bulletsInChamber >= shotsNeeded then shotsNeeded else bulletsInChamber;
        var remainingShots := shotsNeeded - shotsFromChamber;
        var reloadsNeeded := if remainingShots == 0 then 0 else (remainingShots - 1) / k + 1;
        var totalShotsFired := shotsFromChamber + reloadsNeeded * k;
        var bulletsLeft := totalShotsFired - shotsNeeded;
        var nextBullets := if waveIndex + 1 < |waves| then
            var timeGap := waves[waveIndex + 1].start_time - wave.end_time;
            var possibleReloads := timeGap;
            if bulletsLeft == k then bulletsLeft
            else if possibleReloads > 0 then k
            else bulletsLeft
        else bulletsLeft;
        CalculateMinimumBulletsHelper(waves, k, waveIndex + 1, nextBullets)
}
// </vc-helpers>

// <vc-spec>
method SolveMonsterWaves(waves: seq<Wave>, k: nat) returns (result: int)
    requires ValidWaves(waves)
    requires k > 0
    ensures result == -1 <==> !CanSolveAllWaves(waves, k)
    ensures result >= 0 <==> CanSolveAllWaves(waves, k)
    ensures CanSolveAllWaves(waves, k) ==> result == CalculateMinimumBullets(waves, k)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Implementation unchanged from iteration 2 */
{
    if |waves| == 0 {
        return 0;
    }
    
    var canSolve := true;
    var i := 0;
    while i < |waves|
        invariant 0 <= i <= |waves|
        invariant canSolve ==> forall j :: 0 <= j < i ==> CanSolveWave(waves, j, k)
    {
        var wave := waves[i];
        var timeAvailable := wave.end_time - wave.start_time + 1;
        var maxPossibleShots := timeAvailable * k;
        
        if wave.monsters > maxPossibleShots {
            canSolve := false;
            break;
        }
        
        if i > 0 {
            var prevWave := waves[i - 1];
            var timeGap := wave.start_time - prevWave.end_time;
            var reloadsNeeded := CalculateReloadsNeeded(prevWave.monsters, k);
            if reloadsNeeded > timeGap {
                canSolve := false;
                break;
            }
        }
        
        i := i + 1;
    }
    
    if !canSolve {
        assert !CanSolveAllWaves(waves, k);
        return -1;
    }
    
    assert forall j :: 0 <= j < |waves| ==> CanSolveWave(waves, j, k);
    assert CanSolveAllWaves(waves, k);
    result := CalculateMinimumBullets(waves, k);
}
// </vc-code>
