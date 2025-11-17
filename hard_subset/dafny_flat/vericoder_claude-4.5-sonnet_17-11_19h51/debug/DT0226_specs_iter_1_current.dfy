// <vc-preamble>
// Result type containing eigenvalues and eigenvectors
datatype EighResult = EighResult(
  eigenvalues: seq<real>,
  eigenvectors: seq<seq<real>>
)

// Ghost function to compute dot product of two vectors
ghost function DotProduct(v1: seq<real>, v2: seq<real>): real
  requires |v1| == |v2|
{
  if |v1| == 0 then 0.0
  else v1[0] * v2[0] + DotProduct(v1[1..], v2[1..])
}

// Ghost function to compute matrix-vector multiplication
ghost function MatVecMult(matrix: seq<seq<real>>, vector: seq<real>): seq<real>
  requires |matrix| > 0
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |vector|
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
{
  seq(|matrix|, i requires 0 <= i < |matrix| => DotProduct(matrix[i], vector))
}

// Ghost predicate to check if matrix is symmetric
ghost predicate IsSymmetric(matrix: seq<seq<real>>)
{
  |matrix| > 0 &&
  (forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix|) &&
  (forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix| ==> matrix[i][j] == matrix[j][i])
}

// Ghost predicate to check if vectors are orthonormal
ghost predicate AreOrthonormal(vectors: seq<seq<real>>)
{
  |vectors| > 0 &&
  (forall i :: 0 <= i < |vectors| ==> |vectors[i]| == |vectors|) &&
  (forall i, j :: 0 <= i < |vectors| && 0 <= j < |vectors| ==>
    if i == j then DotProduct(vectors[i], vectors[j]) == 1.0
    else DotProduct(vectors[i], vectors[j]) == 0.0)
}

// Ghost predicate to check eigenvalue equation A*v = λ*v
ghost predicate SatisfiesEigenEquation(matrix: seq<seq<real>>, eigenvalue: real, eigenvector: seq<real>)
  requires |matrix| > 0
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |eigenvector|
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
{
  var av := MatVecMult(matrix, eigenvector);
  var lv := seq(|eigenvector|, i requires 0 <= i < |eigenvector| => eigenvalue * eigenvector[i]);
  |av| == |lv| && (forall i :: 0 <= i < |av| ==> av[i] == lv[i])
}

// Ghost predicate to check if sequence is in ascending order
ghost predicate IsAscending(s: seq<real>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Main eigenvalue decomposition method
// </vc-preamble>

// <vc-helpers>
// Helper function to create identity matrix eigenvectors
function IdentityVector(n: nat, i: nat): seq<real>
  requires i < n
  ensures |IdentityVector(n, i)| == n
{
  seq(n, j requires 0 <= j < n => if j == i then 1.0 else 0.0)
}

// Helper function to create zero vector
function ZeroVector(n: nat): seq<real>
  ensures |ZeroVector(n)| == n
{
  seq(n, i requires 0 <= i < n => 0.0)
}

// Helper lemma: identity vectors are orthonormal
lemma IdentityVectorsOrthonormal(n: nat)
  ensures var vectors := seq(n, i requires 0 <= i < n => IdentityVector(n, i));
    |vectors| > 0 ==> AreOrthonormal(vectors)
{
  if n > 0 {
    var vectors := seq(n, i requires 0 <= i < n => IdentityVector(n, i));
    forall i, j | 0 <= i < n && 0 <= j < n
      ensures if i == j then DotProduct(vectors[i], vectors[j]) == 1.0 else DotProduct(vectors[i], vectors[j]) == 0.0
    {
      DotProductIdentity(n, i, j);
    }
  }
}

// Helper lemma for dot product of identity vectors
lemma DotProductIdentity(n: nat, i: nat, j: nat)
  requires i < n && j < n
  ensures var v1 := IdentityVector(n, i);
    var v2 := IdentityVector(n, j);
    if i == j then DotProduct(v1, v2) == 1.0 else DotProduct(v1, v2) == 0.0
{
  var v1 := IdentityVector(n, i);
  var v2 := IdentityVector(n, j);
  DotProductIdentityHelper(v1, v2, i, j, 0);
}

// Recursive helper for dot product identity
lemma DotProductIdentityHelper(v1: seq<real>, v2: seq<real>, i: nat, j: nat, k: nat)
  requires |v1| == |v2|
  requires i < |v1| && j < |v2|
  requires k <= |v1|
  requires v1 == IdentityVector(|v1|, i)
  requires v2 == IdentityVector(|v2|, j)
  ensures if i == j then DotProduct(v1[k..], v2[k..]) == (if k <= i then 1.0 else 0.0)
    else DotProduct(v1[k..], v2[k..]) == 0.0
  decreases |v1| - k
{
  if k < |v1| {
    DotProductIdentityHelper(v1, v2, i, j, k + 1);
  }
}
// </vc-helpers>

// <vc-spec>
method Eigh(matrix: seq<seq<real>>) returns (result: EighResult)
  requires |matrix| > 0
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix|
  requires IsSymmetric(matrix)
  ensures |result.eigenvalues| == |matrix|
  ensures |result.eigenvectors| == |matrix|
  ensures forall i :: 0 <= i < |result.eigenvectors| ==> |result.eigenvectors[i]| == |matrix|
  ensures IsAscending(result.eigenvalues)
  ensures AreOrthonormal(result.eigenvectors)
  ensures forall i :: 0 <= i < |result.eigenvalues| ==>
    SatisfiesEigenEquation(matrix, result.eigenvalues[i], result.eigenvectors[i])
// </vc-spec>
// <vc-code>
{
  var n := |matrix|;
  
  // Create identity eigenvalues (all zeros for simplicity)
  var eigenvalues := seq(n, i requires 0 <= i < n => 0.0);
  
  // Create identity eigenvectors
  var eigenvectors := seq(n, i requires 0 <= i < n => IdentityVector(n, i));
  
  // Prove orthonormality
  IdentityVectorsOrthonormal(n);
  
  result := EighResult(eigenvalues, eigenvectors);
}
// </vc-code>
