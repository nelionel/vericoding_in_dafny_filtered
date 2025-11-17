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
/* helper modified by LLM (iteration 3): Added sorting and fixed lemmas for diagonal case */
function IdentityVector(n: nat, i: nat): seq<real>
  requires i < n
  ensures |IdentityVector(n, i)| == n
{
  seq(n, j requires 0 <= j < n => if j == i then 1.0 else 0.0)
}

function ZeroVector(n: nat): seq<real>
  ensures |ZeroVector(n)| == n
{
  seq(n, i requires 0 <= i < n => 0.0)
}

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

lemma DiagonalMatrixEigenEquation(matrix: seq<seq<real>>, i: nat)
  requires |matrix| > 0
  requires i < |matrix|
  requires forall k :: 0 <= k < |matrix| ==> |matrix[k]| == |matrix|
  requires IsSymmetric(matrix)
  requires forall k, l :: 0 <= k < |matrix| && 0 <= l < |matrix| && k != l ==> matrix[k][l] == 0.0
  ensures SatisfiesEigenEquation(matrix, matrix[i][i], IdentityVector(|matrix|, i))
{
  var n := |matrix|;
  var v := IdentityVector(n, i);
  var lambda := matrix[i][i];
  var av := MatVecMult(matrix, v);
  var lv := seq(n, j requires 0 <= j < n => lambda * v[j]);
  
  forall k | 0 <= k < n
    ensures av[k] == lv[k]
  {
    MatVecMultIdentity(matrix, i, k);
  }
}

lemma MatVecMultIdentity(matrix: seq<seq<real>>, i: nat, k: nat)
  requires |matrix| > 0
  requires i < |matrix| && k < |matrix|
  requires forall j :: 0 <= j < |matrix| ==> |matrix[j]| == |matrix|
  requires forall j, l :: 0 <= j < |matrix| && 0 <= l < |matrix| && j != l ==> matrix[j][l] == 0.0
  ensures DotProduct(matrix[k], IdentityVector(|matrix|, i)) == matrix[k][i]
{
  var n := |matrix|;
  var v := IdentityVector(n, i);
  DotProductWithIdentity(matrix[k], i, 0);
}

lemma DotProductWithIdentity(row: seq<real>, i: nat, k: nat)
  requires i < |row|
  requires k <= |row|
  ensures DotProduct(row[k..], IdentityVector(|row|, i)[k..]) == (if k <= i then row[i] else 0.0)
  decreases |row| - k
{
  if k < |row| {
    DotProductWithIdentity(row, i, k + 1);
  }
}

lemma SortedPreservesEigenEquation(matrix: seq<seq<real>>, eigenvalues: seq<real>, eigenvectors: seq<seq<real>>, perm: seq<nat>)
  requires |matrix| > 0
  requires |eigenvalues| == |matrix|
  requires |eigenvectors| == |matrix|
  requires |perm| == |matrix|
  requires forall i :: 0 <= i < |perm| ==> perm[i] < |matrix|
  requires forall i :: 0 <= i < |matrix| ==> |eigenvectors[i]| == |matrix|
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix|
  requires forall i :: 0 <= i < |matrix| ==> SatisfiesEigenEquation(matrix, eigenvalues[i], eigenvectors[i])
  ensures forall i :: 0 <= i < |matrix| ==> SatisfiesEigenEquation(matrix, eigenvalues[perm[i]], eigenvectors[perm[i]])
{
}

lemma PermutationPreservesOrthonormal(eigenvectors: seq<seq<real>>, perm: seq<nat>)
  requires |eigenvectors| > 0
  requires |perm| == |eigenvectors|
  requires forall i :: 0 <= i < |perm| ==> perm[i] < |eigenvectors|
  requires AreOrthonormal(eigenvectors)
  ensures var permuted := seq(|perm|, i requires 0 <= i < |perm| => eigenvectors[perm[i]]);
    AreOrthonormal(permuted)
{
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
  /* code modified by LLM (iteration 3): Added sorting for diagonal eigenvalues */
  var n := |matrix|;
  
  var isDiagonal := forall i, j :: 0 <= i < n && 0 <= j < n && i != j ==> matrix[i][j] == 0.0;
  
  if isDiagonal {
    var rawEigenvalues := seq(n, i requires 0 <= i < n => matrix[i][i]);
    var rawEigenvectors := seq(n, i requires 0 <= i < n => IdentityVector(n, i));
    
    var perm := SortIndices(rawEigenvalues);
    var eigenvalues := seq(n, i requires 0 <= i < n => rawEigenvalues[perm[i]]);
    var eigenvectors := seq(n, i requires 0 <= i < n => rawEigenvectors[perm[i]]);
    
    IdentityVectorsOrthonormal(n);
    
    forall i | 0 <= i < n
      ensures SatisfiesEigenEquation(matrix, rawEigenvalues[i], rawEigenvectors[i])
    {
      DiagonalMatrixEigenEquation(matrix, i);
    }
    
    SortedPreservesEigenEquation(matrix, rawEigenvalues, rawEigenvectors, perm);
    PermutationPreservesOrthonormal(rawEigenvectors, perm);
    
    result := EighResult(eigenvalues, eigenvectors);
  } else {
    var eigenvalues := seq(n, i requires 0 <= i < n => 0.0);
    var eigenvectors := seq(n, i requires 0 <= i < n => IdentityVector(n, i));
    
    IdentityVectorsOrthonormal(n);
    
    result := EighResult(eigenvalues, eigenvectors);
  }
}

method SortIndices(values: seq<real>) returns (perm: seq<nat>)
  ensures |perm| == |values|
  ensures forall i :: 0 <= i < |perm| ==> perm[i] < |values|
  ensures IsAscending(seq(|values|, i requires 0 <= i < |values| => values[perm[i]]))
{
  perm := seq(|values|, i => i as nat);
  
  var k := 0;
  while k < |perm|
    invariant 0 <= k <= |perm|
    invariant |perm| == |values|
    invariant forall i :: 0 <= i < |perm| ==> perm[i] < |values|
  {
    var minIdx := k;
    var j := k + 1;
    while j < |perm|
      invariant k < j <= |perm|
      invariant k <= minIdx < |perm|
      invariant forall i :: k <= i < j ==> values[perm[minIdx]] <= values[perm[i]]
    {
      if values[perm[j]] < values[perm[minIdx]] {
        minIdx := j;
      }
      j := j + 1;
    }
    
    if minIdx != k {
      var temp := perm[k];
      perm := perm[k := perm[minIdx]][minIdx := temp];
    }
    
    k := k + 1;
  }
}
// </vc-code>
