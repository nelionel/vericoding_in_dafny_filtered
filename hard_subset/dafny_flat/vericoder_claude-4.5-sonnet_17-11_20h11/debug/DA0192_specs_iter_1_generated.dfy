// <vc-preamble>
predicate ValidInput(n: int, k: int) {
  n >= 1 && k >= 2
}

predicate SatisfiesConstraint(x: int, n: int, k: int) {
  x > 0 && k > 0 && (x / k) * (x % k) == n
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
  requires ValidInput(n, k)
  ensures result > 0
  ensures SatisfiesConstraint(result, n, k)
  ensures forall x :: x > 0 && (x / k) * (x % k) == n ==> result <= x
// </vc-spec>
// <vc-code>
{
  var q := 1;
  while q * q < n
    invariant q >= 1
    decreases n - q * q
  {
    q := q + 1;
  }
  
  var r := 1;
  while r * q < n
    invariant r >= 1
    decreases n - r * q
  {
    r := r + 1;
  }
  
  if q * r == n {
    result := q * k + r;
    return;
  }
  
  var best := n * k + 1;
  var q_test := 1;
  
  while q_test <= n
    invariant q_test >= 1
    invariant best > 0
    invariant forall x :: 1 <= x < q_test && x % k < k ==> (x / k) * (x % k) != n || best <= x
    decreases n - q_test + 1
  {
    var r_test := 1;
    while r_test < k
      invariant r_test >= 1
      invariant best > 0
      invariant forall x :: x / k == q_test && 1 <= x % k < r_test ==> (x / k) * (x % k) != n || best <= x
      decreases k - r_test
    {
      if q_test * r_test == n {
        var candidate := q_test * k + r_test;
        if candidate < best {
          best := candidate;
        }
      }
      r_test := r_test + 1;
    }
    q_test := q_test + 1;
  }
  
  result := best;
}
// </vc-code>
