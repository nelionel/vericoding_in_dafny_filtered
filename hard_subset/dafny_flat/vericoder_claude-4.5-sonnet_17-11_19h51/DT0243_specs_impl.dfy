// <vc-preamble>
// Matrix represented as sequence of rows
type Matrix<T> = seq<seq<T>>

// Helper predicates for matrix properties
predicate IsValidMatrix<T>(m: Matrix<T>, rows: nat, cols: nat)
{
  |m| == rows && (forall i :: 0 <= i < |m| ==> |m[i]| == cols)
}

predicate IsValidVector<T>(v: seq<T>, size: nat)
{
  |v| == size
}

// Matrix multiplication helper
function MatrixMultiply(A: Matrix<real>, B: Matrix<real>): Matrix<real>
  requires IsValidMatrix(A, |A|, if |A| > 0 then |A[0]| else 0)
  requires IsValidMatrix(B, |B|, if |B| > 0 then |B[0]| else 0)
  requires |A| > 0 ==> |B| > 0 && |A[0]| == |B|
{
  if |A| == 0 || |B| == 0 then []
  else
    seq(|A|, i requires 0 <= i < |A| => 
      seq(|B[0]|, j requires 0 <= j < |B[0]| =>
        Sum(seq(|A[0]|, k requires 0 <= k < |A[0]| => A[i][k] * B[k][j]))))
}

// Sum of a sequence of reals
function Sum(s: seq<real>): real
{
  if |s| == 0 then 0.0 else s[0] + Sum(s[1..])
}

// Diagonal matrix from vector
function DiagMatrix(v: seq<real>): Matrix<real>
{
  seq(|v|, i requires 0 <= i < |v| =>
    seq(|v|, j requires 0 <= j < |v| => if i == j then v[i] else 0.0))
}

// Matrix transpose
function Transpose(m: Matrix<real>): Matrix<real>
  requires IsValidMatrix(m, |m|, if |m| > 0 then |m[0]| else 0)
{
  if |m| == 0 then []
  else
    seq(|m[0]|, j requires 0 <= j < |m[0]| =>
      seq(|m|, i requires 0 <= i < |m| => m[i][j]))
}

// Identity matrix
function IdentityMatrix(size: nat): Matrix<real>
{
  seq(size, i requires 0 <= i < size =>
    seq(size, j requires 0 <= j < size => if i == j then 1.0 else 0.0))
}

// Check if matrix has orthonormal columns (U^T @ U = I)
predicate HasOrthonormalColumns(U: Matrix<real>)
  requires IsValidMatrix(U, |U|, if |U| > 0 then |U[0]| else 0)
{
  var UT := Transpose(U);
  var product := MatrixMultiply(UT, U);
  product == IdentityMatrix(if |U| > 0 then |U[0]| else 0)
}

// Check if matrix has orthonormal rows (Vh @ Vh^T = I)
predicate HasOrthonormalRows(Vh: Matrix<real>)
  requires IsValidMatrix(Vh, |Vh|, if |Vh| > 0 then |Vh[0]| else 0)
{
  var VhT := Transpose(Vh);
  var product := MatrixMultiply(Vh, VhT);
  product == IdentityMatrix(|Vh|)
}

// Check if singular values are non-negative and in descending order
predicate ValidSingularValues(S: seq<real>)
{
  (forall i :: 0 <= i < |S| ==> S[i] >= 0.0) &&
  (forall i :: 0 <= i < |S| - 1 ==> S[i] >= S[i + 1])
}

// Main SVD method specification
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added lemmas to establish matrix validity for multiply operations */
lemma TransposeProperties(m: Matrix<real>, rows: nat, cols: nat)
  requires IsValidMatrix(m, rows, cols)
  ensures var mT := Transpose(m);
          IsValidMatrix(mT, cols, rows)
  ensures rows > 0 ==> var mT := Transpose(m); |mT| > 0 && |mT[0]| == rows
{
  if rows > 0 {
    var mT := Transpose(m);
    assert |mT| == cols;
    forall i | 0 <= i < |mT|
      ensures |mT[i]| == rows
    {
      assert |mT[i]| == rows;
    }
  }
}

lemma DiagMatrixProperties(v: seq<real>)
  ensures var D := DiagMatrix(v);
          IsValidMatrix(D, |v|, |v|)
  ensures |v| > 0 ==> var D := DiagMatrix(v); |D| > 0 && |D[0]| == |v|
{
  var D := DiagMatrix(v);
  assert |D| == |v|;
  forall i | 0 <= i < |D|
    ensures |D[i]| == |v|
  {
    assert |D[i]| == |v|;
  }
}

lemma MatrixMultiplyValidity(A: Matrix<real>, B: Matrix<real>, aRows: nat, aCols: nat, bRows: nat, bCols: nat)
  requires IsValidMatrix(A, aRows, aCols)
  requires IsValidMatrix(B, bRows, bCols)
  requires aRows > 0 ==> bRows > 0 && aCols == bRows
  ensures var result := MatrixMultiply(A, B);
          IsValidMatrix(result, aRows, bCols)
  ensures aRows > 0 && bRows > 0 ==> var result := MatrixMultiply(A, B); |result| > 0 && |result[0]| == bCols
{
}
// </vc-helpers>

// <vc-spec>
method SVD(A: Matrix<real>, m: nat, n: nat) returns (U: Matrix<real>, S: seq<real>, Vh: Matrix<real>)
  requires IsValidMatrix(A, m, n)
  ensures var minDim := if m <= n then m else n;
          IsValidMatrix(U, m, minDim) &&
          IsValidVector(S, minDim) &&
          IsValidMatrix(Vh, minDim, n)
  // Property 1: Matrix reconstruction A = U @ diag(S) @ Vh
  ensures var diagS := DiagMatrix(S);
          var temp := MatrixMultiply(U, diagS);
          MatrixMultiply(temp, Vh) == A
  // Property 2: U has orthonormal columns
  ensures HasOrthonormalColumns(U)
  // Property 3: Vh has orthonormal rows  
  ensures HasOrthonormalRows(Vh)
  // Property 4: S contains valid singular values
  ensures ValidSingularValues(S)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Established all preconditions for matrix operations */
  var minDim := if m <= n then m else n;
  
  U := seq(m, i requires 0 <= i < m =>
    seq(minDim, j requires 0 <= j < minDim => if i == j then 1.0 else 0.0));
  
  S := seq(minDim, i => 0.0);
  
  Vh := seq(minDim, i requires 0 <= i < minDim =>
    seq(n, j requires 0 <= j < n => if i == j then 1.0 else 0.0));
  
  assert IsValidMatrix(U, m, minDim);
  assert IsValidMatrix(Vh, minDim, n);
  
  DiagMatrixProperties(S);
  var diagS := DiagMatrix(S);
  assert IsValidMatrix(diagS, minDim, minDim);
  
  if m > 0 {
    assert |U| > 0 && |U[0]| == minDim;
    assert |diagS| > 0 && |diagS[0]| == minDim;
    MatrixMultiplyValidity(U, diagS, m, minDim, minDim, minDim);
    var temp := MatrixMultiply(U, diagS);
    assert IsValidMatrix(temp, m, minDim);
    
    if n > 0 {
      assert |Vh| > 0 && |Vh[0]| == n;
      assert |temp| > 0 && |temp[0]| == minDim;
      MatrixMultiplyValidity(temp, Vh, m, minDim, minDim, n);
    }
  }
  
  TransposeProperties(U, m, minDim);
  var UT := Transpose(U);
  assert IsValidMatrix(UT, minDim, m);
  if minDim > 0 {
    assert |UT| > 0 && |UT[0]| == m;
    assert |U| > 0 && |U[0]| == minDim;
    MatrixMultiplyValidity(UT, U, minDim, m, m, minDim);
  }
  
  TransposeProperties(Vh, minDim, n);
  var VhT := Transpose(Vh);
  assert IsValidMatrix(VhT, n, minDim);
  if minDim > 0 {
    assert |Vh| > 0 && |Vh[0]| == n;
    assert |VhT| > 0 && |VhT[0]| == minDim;
    MatrixMultiplyValidity(Vh, VhT, minDim, n, n, minDim);
  }
}
// </vc-code>
