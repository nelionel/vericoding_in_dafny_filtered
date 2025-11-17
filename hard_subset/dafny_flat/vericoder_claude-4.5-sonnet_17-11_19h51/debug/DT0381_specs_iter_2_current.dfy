// <vc-preamble>
// Represents a Chebyshev series as coefficients from lowest to highest order
type ChebSeries = seq<real>

// Helper predicate to check if a series is effectively zero (all coefficients are zero)
predicate IsZeroSeries(c: ChebSeries)
{
    forall i :: 0 <= i < |c| ==> c[i] == 0.0
}

// Get the effective degree of a Chebyshev series (highest non-zero coefficient index)
function EffectiveDegree(c: ChebSeries): int
    requires |c| > 0
{
    if IsZeroSeries(c) then -1
    else EffectiveDegreeHelper(c, |c| - 1)
}

function EffectiveDegreeHelper(c: ChebSeries, i: int): int
    requires 0 <= i < |c|
    decreases i
{
    if c[i] != 0.0 then i
    else if i == 0 then -1
    else EffectiveDegreeHelper(c, i - 1)
}

// Chebyshev polynomial evaluation at a point x
function ChebEval(c: ChebSeries, x: real): real
    requires |c| > 0
    decreases |c|
{
    if |c| == 1 then c[0]
    else if |c| == 2 then c[0] + c[1] * x
    else
        // T_n(x) = 2*x*T_{n-1}(x) - T_{n-2}(x)
        c[0] + c[1] * x + (c[2] * (2.0 * x * x - 1.0)) + ChebEvalRec(c[3..], x, x, 1.0)
}

function ChebEvalRec(c: seq<real>, x: real, t_prev: real, t_curr: real): real
    decreases |c|
{
    if |c| == 0 then 0.0
    else
        var t_next := 2.0 * x * t_curr - t_prev;
        c[0] * t_next + ChebEvalRec(c[1..], x, t_curr, t_next)
}

// Polynomial addition in Chebyshev basis
function ChebAdd(c1: ChebSeries, c2: ChebSeries): ChebSeries
{
    var maxLen := if |c1| > |c2| then |c1| else |c2|;
    seq(maxLen, i => 
        (if i < |c1| then c1[i] else 0.0) + 
        (if i < |c2| then c2[i] else 0.0))
}

// Polynomial multiplication in Chebyshev basis
function ChebMul(c1: ChebSeries, c2: ChebSeries): ChebSeries
{
    [0.0]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added helper to pad sequence to target length */
function PadSeq(c: ChebSeries, len: int): ChebSeries
  requires len >= 0
  ensures |PadSeq(c, len)| == len
  ensures forall i :: 0 <= i < len ==> PadSeq(c, len)[i] == (if i < |c| then c[i] else 0.0)
{
  seq(len, i => if i < |c| then c[i] else 0.0)
}
// </vc-helpers>

// <vc-spec>
method ChebDiv(c1: ChebSeries, c2: ChebSeries) returns (quotient: ChebSeries, remainder: ChebSeries)
    requires |c1| > 0 && |c2| > 0
    requires !IsZeroSeries(c2)  // Divisor must be non-zero
    requires c2[|c2|-1] != 0.0  // Leading coefficient must be non-zero
    
    // Both outputs have same size as dividend (with zero-padding)
    ensures |quotient| == |c1| && |remainder| == |c1|
    
    // Division algorithm: c1 = c2 * quotient + remainder
    ensures forall x: real :: ChebEval(c1, x) == ChebEval(ChebAdd(ChebMul(c2, quotient), remainder), x)
    
    // Remainder degree constraint: effective degree of remainder < effective degree of c2
    ensures EffectiveDegree(remainder) < EffectiveDegree(c2)
    
    // Special case: if degree(c1) < degree(c2), then quotient = 0 and remainder = c1 (zero-padded)
    ensures EffectiveDegree(c1) < EffectiveDegree(c2) ==> 
        IsZeroSeries(quotient) && 
        (forall i :: 0 <= i < |c1| ==> 
            remainder[i] == (if i < |c1| then c1[i] else 0.0))
    
    // Special case: if c2 is constant (degree 0), then remainder = 0
    ensures EffectiveDegree(c2) == 0 ==> 
        IsZeroSeries(remainder) &&
        (forall i :: 0 <= i < |c1| ==> quotient[i] == c1[i] / c2[0])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed index out of range errors and verification issues */
  var deg1 := EffectiveDegree(c1);
  var deg2 := EffectiveDegree(c2);
  
  quotient := seq(|c1|, i => 0.0);
  remainder := PadSeq(c1, |c1|);
  
  if deg1 < deg2 {
    return;
  }
  
  if deg2 == 0 {
    var divisor := c2[0];
    quotient := seq(|c1|, i => c1[i] / divisor);
    remainder := seq(|c1|, i => 0.0);
    return;
  }
  
  var q := seq(|c1|, i => 0.0);
  var r := PadSeq(c1, |c1|);
  
  var currentDeg := deg1;
  var leadingCoeff := c2[deg2];
  
  while currentDeg >= deg2
    decreases currentDeg
    invariant -1 <= currentDeg <= deg1
    invariant |q| == |c1| && |r| == |c1|
  {
    var rDeg := EffectiveDegree(r);
    if rDeg < deg2 {
      break;
    }
    
    if rDeg >= |r| {
      break;
    }
    
    var coeff := r[rDeg] / leadingCoeff;
    q := q[rDeg := coeff];
    
    var pos := rDeg - deg2;
    var j := 0;
    while j <= deg2
      decreases deg2 - j
      invariant 0 <= j <= deg2 + 1
      invariant |r| == |c1|
    {
      if pos + j < |r| && j < |c2| {
        r := r[pos + j := r[pos + j] - coeff * c2[j]];
      }
      j := j + 1;
    }
    
    currentDeg := currentDeg - 1;
  }
  
  quotient := q;
  remainder := r;
}
// </vc-code>
