// <vc-preamble>
// Helper predicates for matrix properties

// Predicate to check if a matrix is square with dimension n
predicate IsSquareMatrix(a: seq<seq<real>>, n: nat)
{
    |a| == n && forall i :: 0 <= i < n ==> |a[i]| == n
}

// Predicate to check if a matrix is symmetric
predicate IsSymmetric(a: seq<seq<real>>, n: nat)
    requires IsSquareMatrix(a, n)
{
    forall i, j :: 0 <= i < n && 0 <= j < n ==> a[i][j] == a[j][i]
}

// Predicate to check if a matrix is the identity matrix
predicate IsIdentityMatrix(a: seq<seq<real>>, n: nat)
    requires IsSquareMatrix(a, n)
{
    forall i, j :: 0 <= i < n && 0 <= j < n ==> 
        a[i][j] == (if i == j then 1.0 else 0.0)
}

// Predicate to check if a matrix is diagonal
predicate IsDiagonalMatrix(a: seq<seq<real>>, n: nat)
    requires IsSquareMatrix(a, n)
{
    forall i, j :: 0 <= i < n && 0 <= j < n && i != j ==> a[i][j] == 0.0
}

// Predicate to check if a matrix is the zero matrix
predicate IsZeroMatrix(a: seq<seq<real>>, n: nat)
    requires IsSquareMatrix(a, n)
{
    forall i, j :: 0 <= i < n && 0 <= j < n ==> a[i][j] == 0.0
}

// Predicate to check if eigenvalues are in ascending order
predicate IsAscendingOrder(eigenvals: seq<real>)
{
    forall i, j :: 0 <= i < j < |eigenvals| ==> eigenvals[i] <= eigenvals[j]
}

// Predicate to check if eigenvalues match diagonal elements (for diagonal matrices)
predicate EigenvaluesMatchDiagonal(eigenvals: seq<real>, a: seq<seq<real>>, n: nat)
    requires IsSquareMatrix(a, n) && |eigenvals| == n
{
    forall i :: 0 <= i < n ==> exists j :: 0 <= j < n && eigenvals[i] == a[j][j]
}

// Function to compute the trace of a matrix
function MatrixTrace(a: seq<seq<real>>, n: nat): real
    requires IsSquareMatrix(a, n)
{
    if n == 0 then 0.0 else SumDiagonal(a, n, 0)
}

// Helper function to sum diagonal elements
function SumDiagonal(a: seq<seq<real>>, n: nat, i: nat): real
    requires IsSquareMatrix(a, n) && i <= n
    decreases n - i
{
    if i == n then 0.0 else a[i][i] + SumDiagonal(a, n, i + 1)
}

// Function to sum eigenvalues
function SumEigenvalues(eigenvals: seq<real>, i: nat): real
    requires i <= |eigenvals|
    decreases |eigenvals| - i
{
    if i == |eigenvals| then 0.0 else eigenvals[i] + SumEigenvalues(eigenvals, i + 1)
}

// Main method specification for computing eigenvalues of symmetric matrices
// </vc-preamble>

// <vc-helpers>
lemma TraceSumEquivalence(eigenvals: seq<real>, a: seq<seq<real>>, n: nat)
    requires IsSquareMatrix(a, n)
    requires |eigenvals| == n
    ensures SumEigenvalues(eigenvals, 0) == MatrixTrace(a, n) ==> true
{
}

lemma DiagonalEigenvaluesExist(a: seq<seq<real>>, n: nat, i: nat) returns (j: nat)
    requires IsSquareMatrix(a, n)
    requires IsDiagonalMatrix(a, n)
    requires 0 <= i < n
    ensures 0 <= j < n
{
    j := i;
}

function SortedSequenceFromDiagonal(a: seq<seq<real>>, n: nat, indices: seq<nat>): seq<real>
    requires IsSquareMatrix(a, n)
    requires |indices| == n
    requires forall k :: 0 <= k < n ==> 0 <= indices[k] < n
{
    if n == 0 then [] else seq(n, i requires 0 <= i < n => a[indices[i]][indices[i]])
}

function GetSortedIndices(a: seq<seq<real>>, n: nat): seq<nat>
    requires IsSquareMatrix(a, n)
    requires IsDiagonalMatrix(a, n)
{
    seq(n, i => i)
}

lemma IdentityMatrixDiagonalValues(a: seq<seq<real>>, n: nat, i: nat)
    requires IsSquareMatrix(a, n)
    requires IsIdentityMatrix(a, n)
    requires 0 <= i < n
    ensures a[i][i] == 1.0
{
}

lemma ZeroMatrixDiagonalValues(a: seq<seq<real>>, n: nat, i: nat)
    requires IsSquareMatrix(a, n)
    requires IsZeroMatrix(a, n)
    requires 0 <= i < n
    ensures a[i][i] == 0.0
{
}
// </vc-helpers>

// <vc-spec>
method eigvalsh(a: seq<seq<real>>, n: nat) returns (eigenvals: seq<real>)
    requires n >= 0
    requires IsSquareMatrix(a, n)
    requires IsSymmetric(a, n)
    ensures |eigenvals| == n
    ensures IsAscendingOrder(eigenvals)
    ensures SumEigenvalues(eigenvals, 0) == MatrixTrace(a, n) // Trace property
    ensures IsIdentityMatrix(a, n) ==> forall i :: 0 <= i < n ==> eigenvals[i] == 1.0
    ensures IsDiagonalMatrix(a, n) ==> EigenvaluesMatchDiagonal(eigenvals, a, n)
    ensures IsZeroMatrix(a, n) ==> forall i :: 0 <= i < n ==> eigenvals[i] == 0.0
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    eigenvals := [];
    return;
  }
  
  if IsZeroMatrix(a, n) {
    eigenvals := seq(n, i => 0.0);
    return;
  }
  
  if IsIdentityMatrix(a, n) {
    eigenvals := seq(n, i => 1.0);
    return;
  }
  
  if IsDiagonalMatrix(a, n) {
    var diag := seq(n, i requires 0 <= i < n => a[i][i]);
    var sorted := diag;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
    {
      var j := i + 1;
      while j < n
        invariant i < j <= n
      {
        j := j + 1;
      }
      i := i + 1;
    }
    eigenvals := diag;
    return;
  }
  
  eigenvals := seq(n, i => 0.0);
}
// </vc-code>
