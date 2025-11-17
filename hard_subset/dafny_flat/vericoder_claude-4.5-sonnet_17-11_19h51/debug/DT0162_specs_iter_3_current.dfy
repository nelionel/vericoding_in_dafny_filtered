// <vc-preamble>
// Trigonometric functions (uninterpreted in Dafny)
function cos(x: real): real

function sin(x: real): real

// Complex number representation for FFT results
datatype Complex = Complex(re: real, im: real)

// Complex arithmetic operations
function ComplexAdd(z1: Complex, z2: Complex): Complex
{
    Complex(z1.re + z2.re, z1.im + z2.im)
}

function ComplexMul(z1: Complex, z2: Complex): Complex
{
    Complex(z1.re * z2.re - z1.im * z2.im, z1.re * z2.im + z1.im * z2.re)
}

function ComplexExp(theta: real): Complex
{
    Complex(cos(theta), sin(theta))
}

function RealToComplex(x: real): Complex
{
    Complex(x, 0.0)
}

// Sum over a range with a given function
function {:opaque} SumRange(start: int, end: int, f: int -> Complex): Complex
    requires start <= end
    decreases end - start
{
    if start >= end then Complex(0.0, 0.0)
    else ComplexAdd(f(start), SumRange(start + 1, end, f))
}

// 2D DFT computation for a specific output element
function Rfft2Element(input: seq<seq<real>>, m: int, n: int, k: int, l: int): Complex
    requires m >= 0 && n >= 0
    requires |input| == m + 1
    requires forall i :: 0 <= i < |input| ==> |input[i]| == n + 1
    requires 0 <= k <= m
    requires 0 <= l <= n / 2
{
    SumRange(0, m + 1, p =>
        SumRange(0, n + 1, q =>
            var phase := -2.0 * 3.14159265358979323846 * 
                        (k as real * p as real / (m + 1) as real + 
                         l as real * q as real / (n + 1) as real);
            var weight := ComplexExp(phase);
            ComplexMul(RealToComplex(input[p][q]), weight)))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed lemmas to handle actual Rfft2Element preconditions properly */
lemma DCComponentIsReal(input: seq<seq<real>>, m: int, n: int)
  requires m >= 0 && n >= 0
  requires |input| == m + 1
  requires forall i :: 0 <= i < |input| ==> |input[i]| == n + 1
  ensures Rfft2Element(input, m, n, 0, 0).im == 0.0
{
}

lemma ZeroInputGivesZeroOutput(input: seq<seq<real>>, m: int, n: int, k: int, l: int)
  requires m >= 0 && n >= 0
  requires |input| == m + 1
  requires forall i :: 0 <= i < |input| ==> |input[i]| == n + 1
  requires 0 <= k <= m
  requires 0 <= l <= n / 2
  requires forall i, j :: 0 <= i < |input| && 0 <= j < |input[i]| ==> input[i][j] == 0.0
  ensures Rfft2Element(input, m, n, k, l) == Complex(0.0, 0.0)
{
}

lemma BoundProperty(input: seq<seq<real>>, m: int, n: int, k: int, l: int)
  requires m >= 0 && n >= 0
  requires |input| == m + 1
  requires forall i :: 0 <= i < |input| ==> |input[i]| == n + 1
  requires 0 <= k <= m
  requires 0 <= l <= n / 2
  ensures (var res := Rfft2Element(input, m, n, k, l);
           var absRe := if res.re >= 0.0 then res.re else -res.re;
           var sum := SumRange(0, m + 1, p => SumRange(0, n + 1, q => RealToComplex(input[p][q])));
           var absSum := if sum.re >= 0.0 then sum.re else -sum.re;
           absRe <= absSum * (m + 1) as real * (n + 1) as real)
{
}
// </vc-helpers>

// <vc-spec>
method rfft2(input: seq<seq<real>>) returns (result: seq<seq<Complex>>)
    // Input constraints: must be a valid 2D array
    requires |input| > 0
    requires forall i :: 0 <= i < |input| ==> |input[i]| > 0
    requires forall i :: 0 <= i < |input| ==> |input[i]| == |input[0]|
    
    // Output shape constraints
    ensures |result| == |input|  // Same number of rows
    ensures |result| > 0
    ensures forall i :: 0 <= i < |result| ==> 
        |result[i]| == |input[0]| / 2 + 1  // Reduced columns due to Hermitian symmetry
    
    // Mathematical correctness: each element computed via 2D DFT formula
    ensures forall k, l :: 0 <= k < |result| && 0 <= l < |result[k]| ==>
        result[k][l] == Rfft2Element(input, |input| - 1, |input[0]| - 1, k, l)
    
    // DC component (0,0) is real - imaginary part is zero
    ensures result[0][0].im == 0.0
    
    // Energy conservation property for zero input
    ensures (forall i, j :: 0 <= i < |input| && 0 <= j < |input[i]| ==> input[i][j] == 0.0) ==>
            (forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==> 
             result[i][j] == Complex(0.0, 0.0))
    
    // Linearity property structure (the transform preserves linear combinations)
    ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==>
        (if result[i][j].re >= 0.0 then result[i][j].re else -result[i][j].re) <= 
        (var sum := SumRange(0, |input|, p => SumRange(0, |input[0]|, q => RealToComplex(input[p][q]))); 
         if sum.re >= 0.0 then sum.re else -sum.re) * |input| as real * |input[0]| as real
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed bounds to match Rfft2Element preconditions and use correct indices */
{
  var m := |input| - 1;
  var n := |input[0]| - 1;
  var numRows := |input|;
  var numCols := n / 2 + 1;
  
  result := [];
  var k := 0;
  while k < numRows
    invariant 0 <= k <= numRows
    invariant |result| == k
    invariant forall i :: 0 <= i < k ==> |result[i]| == numCols
    invariant forall i, j :: 0 <= i < k && 0 <= j < |result[i]| ==>
      result[i][j] == Rfft2Element(input, m, n, i, j)
  {
    var row: seq<Complex> := [];
    var l := 0;
    while l < numCols
      invariant 0 <= l <= numCols
      invariant |row| == l
      invariant forall j :: 0 <= j < l ==>
        row[j] == Rfft2Element(input, m, n, k, j)
    {
      assert 0 <= k <= m;
      assert 0 <= l <= n / 2;
      var element := Rfft2Element(input, m, n, k, l);
      row := row + [element];
      l := l + 1;
    }
    result := result + [row];
    k := k + 1;
  }
  
  DCComponentIsReal(input, m, n);
  
  if forall i, j :: 0 <= i < |input| && 0 <= j < |input[i]| ==> input[i][j] == 0.0 {
    forall i, j | 0 <= i < |result| && 0 <= j < |result[i]|
      ensures result[i][j] == Complex(0.0, 0.0)
    {
      assert 0 <= i <= m;
      assert 0 <= j <= n / 2;
      ZeroInputGivesZeroOutput(input, m, n, i, j);
    }
  }
  
  forall i, j | 0 <= i < |result| && 0 <= j < |result[i]|
    ensures (if result[i][j].re >= 0.0 then result[i][j].re else -result[i][j].re) <=
            (var sum := SumRange(0, |input|, p => SumRange(0, |input[0]|, q => RealToComplex(input[p][q])));
             if sum.re >= 0.0 then sum.re else -sum.re) * |input| as real * |input[0]| as real
  {
    assert 0 <= i <= m;
    assert 0 <= j <= n / 2;
    BoundProperty(input, m, n, i, j);
  }
}
// </vc-code>
