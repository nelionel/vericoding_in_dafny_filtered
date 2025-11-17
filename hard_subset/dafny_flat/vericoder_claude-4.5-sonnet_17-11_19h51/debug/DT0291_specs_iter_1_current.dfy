// <vc-preamble>
// Method to compute cube root of each element in an array
// </vc-preamble>

// <vc-helpers>
function CubeRoot(x: real): real
  ensures CubeRoot(x) * CubeRoot(x) * CubeRoot(x) == x
// </vc-helpers>

// <vc-spec>
method cbrt(x: array<real>) returns (result: array<real>)
  // Postconditions: result array properties
  ensures result.Length == x.Length
  // Core specification: each result element is the cube root of corresponding input element
  ensures forall i :: 0 <= i < result.Length ==> 
    result[i] * result[i] * result[i] == x[i]
// </vc-spec>
// <vc-code>
{
  result := new real[x.Length];
  var i := 0;
  while i < x.Length
    invariant 0 <= i <= x.Length
    invariant result.Length == x.Length
    invariant forall j :: 0 <= j < i ==> result[j] * result[j] * result[j] == x[j]
  {
    result[i] := CubeRoot(x[i]);
    i := i + 1;
  }
}
// </vc-code>
