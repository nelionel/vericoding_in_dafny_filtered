// <vc-preamble>
// Complex number representation
datatype Complex = Complex(re: real, im: real)

// Complex number zero
function ComplexZero(): Complex
{
    Complex(0.0, 0.0)
}

// Complex number addition
function ComplexAdd(z: Complex, w: Complex): Complex
{
    Complex(z.re + w.re, z.im + w.im)
}

// Complex number multiplication
function ComplexMul(z: Complex, w: Complex): Complex
{
    Complex(z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re)
}

// Complex exponential function e^(i*theta) = cos(theta) + i*sin(theta)
// Note: Using placeholder implementation since Dafny lacks trigonometric functions
function ComplexExp(theta: real): Complex
{
    Complex(theta - theta*theta*theta/6.0, theta - theta*theta/2.0) // Taylor series approximation placeholder
}

// Recursive sum of complex numbers over range [0, n)
function {:opaque} ComplexSum(n: nat, f: nat -> Complex): Complex
    decreases n
{
    if n == 0 then ComplexZero()
    else ComplexAdd(f(n-1), ComplexSum(n-1, f))
}

// Pi constant approximation
const PI: real := 3.14159265358979323846

/**
 * Fast Fourier Transform method
 * Computes the one-dimensional discrete Fourier Transform of the input sequence
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed partial function requirements, made functions total */
function ComplexSumSeq(s: seq<Complex>): Complex
{
  if |s| == 0 then ComplexZero()
  else ComplexAdd(s[0], ComplexSumSeq(s[1..]))
}

lemma ComplexSumEquivalence(n: nat, f: nat -> Complex)
  ensures ComplexSum(n, f) == ComplexSumSeq(seq(n, f))
{
  reveal ComplexSum();
  if n == 0 {
  } else {
    ComplexSumEquivalence(n-1, f);
  }
}

function DFTElement(a: seq<Complex>, k: nat): Complex
  requires k < |a|
{
  var n := |a|;
  ComplexSum(n, (j: nat) => if j < n then ComplexMul(a[j], ComplexExp(-2.0 * PI * (k as real) * (j as real) / (n as real))) else ComplexZero())
}

lemma DFTZeroCase(a: seq<Complex>)
  requires |a| > 0
  ensures DFTElement(a, 0) == ComplexSum(|a|, (j: nat) => if j < |a| then a[j] else ComplexZero())
{
  reveal ComplexSum();
  var n := |a|;
  assert forall j :: 0 <= j < n ==> ComplexExp(-2.0 * PI * 0.0 * (j as real) / (n as real)) == ComplexExp(0.0) by {
    forall j | 0 <= j < n
      ensures ComplexExp(-2.0 * PI * 0.0 * (j as real) / (n as real)) == ComplexExp(0.0)
    {
      assert -2.0 * PI * 0.0 * (j as real) / (n as real) == 0.0;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method FFT(a: seq<Complex>) returns (result: seq<Complex>)
    requires |a| > 0
    ensures |result| == |a|
    // Each output element k is computed according to the DFT formula
    ensures forall k :: 0 <= k < |a| ==> 
        result[k] == ComplexSum(|a|, (j: nat) requires 0 <= j < |a| => 
            ComplexMul(a[j], ComplexExp(-2.0 * PI * (k as real) * (j as real) / (|a| as real))))
    // DC component preservation (k=0 case)
    ensures result[0] == ComplexSum(|a|, (j: nat) requires 0 <= j < |a| => a[j])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): using total functions instead of partial */
{
  var n := |a|;
  result := seq(n, (k: nat) requires 0 <= k < n => DFTElement(a, k));
  
  forall k | 0 <= k < n
    ensures result[k] == ComplexSum(n, (j: nat) => if j < n then ComplexMul(a[j], ComplexExp(-2.0 * PI * (k as real) * (j as real) / (n as real))) else ComplexZero())
  {
    assert result[k] == DFTElement(a, k);
  }
  
  DFTZeroCase(a);
  assert result[0] == DFTElement(a, 0);
  assert result[0] == ComplexSum(|a|, (j: nat) => if j < |a| then a[j] else ComplexZero());
}
// </vc-code>
