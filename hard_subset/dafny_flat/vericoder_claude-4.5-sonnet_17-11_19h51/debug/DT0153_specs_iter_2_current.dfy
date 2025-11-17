// <vc-preamble>
// Complex number datatype with real and imaginary components
datatype Complex = Complex(re: real, im: real)

// Complex number arithmetic operations
function ComplexAdd(z1: Complex, z2: Complex): Complex
{
    Complex(z1.re + z2.re, z1.im + z2.im)
}

function ComplexMul(z1: Complex, z2: Complex): Complex
{
    Complex(z1.re * z2.re - z1.im * z2.im, z1.re * z2.im + z1.im * z2.re)
}

function ComplexScale(s: real, z: Complex): Complex
{
    Complex(s * z.re, s * z.im)
}

// Complex exponential function: e^(i*theta) = cos(theta) + i*sin(theta)
function ComplexExp(theta: real): Complex
{
    Complex(Math.Cos(theta), Math.Sin(theta))
}

// Mathematical constants
const PI: real := 3.14159265358979323846

// Sum of complex numbers over a range with a function
function ComplexSum(n: nat, f: int -> Complex): Complex
    requires n >= 0
    decreases n
{
    if n == 0 then Complex(0.0, 0.0)
    else ComplexAdd(f(n-1), ComplexSum(n-1, f))
}

// Convert natural number to real
function NatToReal(n: nat): real
{
    n as real
}

// Main IFFT method specification
// Mathematical library functions (assumed to exist)
class Math
{
    static function Cos(x: real): real
    {
        0.0  // Placeholder implementation
    }
    
    static function Sin(x: real): real
    {
        0.0  // Placeholder implementation
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed index bounds and preconditions */
function GetIFFTTerm(a: seq<Complex>, k: nat, j: nat, n: nat): Complex
    requires n > 0
    requires k < n
    requires j < |a|
    requires n <= |a|
{
    ComplexMul(a[j], ComplexExp(2.0 * PI * NatToReal(k) * NatToReal(j) / NatToReal(n)))
}

function ComputeIFFTSum(a: seq<Complex>, k: nat, n: nat): Complex
    requires n > 0
    requires k < n
    requires n <= |a|
    decreases n
{
    if n == 0 then Complex(0.0, 0.0)
    else if n == 1 then GetIFFTTerm(a, k, 0, n)
    else ComplexAdd(GetIFFTTerm(a, k, n-1, n), ComputeIFFTSum(a, k, n-1))
}

lemma IFFTSumEquivalence(a: seq<Complex>, k: nat, n: nat)
    requires n > 0
    requires k < n
    requires n <= |a|
    ensures ComputeIFFTSum(a, k, n) == ComplexSum(n, j => ComplexMul(a[j], ComplexExp(2.0 * PI * NatToReal(k) * NatToReal(j) / NatToReal(n))))
    decreases n
{
    if n == 1 {
    } else {
        IFFTSumEquivalence(a, k, n-1);
    }
}
// </vc-helpers>

// <vc-spec>
method IFFT(a: seq<Complex>) returns (result: seq<Complex>)
    requires |a| > 0
    ensures |result| == |a|
    ensures forall k :: 0 <= k < |result| ==>
        result[k] == ComplexScale(1.0 / NatToReal(|a|), 
            ComplexSum(|a|, j => 
                ComplexMul(a[j], 
                    ComplexExp(2.0 * PI * NatToReal(k) * NatToReal(j) / NatToReal(|a|)))))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed preconditions for helper calls */
    var n := |a|;
    result := [];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==>
            result[k] == ComplexScale(1.0 / NatToReal(n),
                ComplexSum(n, j =>
                    ComplexMul(a[j],
                        ComplexExp(2.0 * PI * NatToReal(k) * NatToReal(j) / NatToReal(n)))))
    {
        var sum := ComputeIFFTSum(a, i, n);
        IFFTSumEquivalence(a, i, n);
        var scaled := ComplexScale(1.0 / NatToReal(n), sum);
        result := result + [scaled];
        i := i + 1;
    }
}
// </vc-code>
