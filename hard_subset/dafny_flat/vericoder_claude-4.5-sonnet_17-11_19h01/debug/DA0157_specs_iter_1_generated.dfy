// <vc-preamble>
predicate ValidInput(n: int, a: int, b: int)
{
  n > 0 && a > 0 && b > 0
}

predicate ValidOutput(result: seq<int>, n: int, a: int, b: int)
{
  |result| == 3 &&
  result[0] >= 6 * n &&
  result[1] > 0 && result[2] > 0 &&
  result[0] == result[1] * result[2] &&
  ((result[1] >= a && result[2] >= b) || (result[1] >= b && result[2] >= a))
}
// </vc-preamble>

// <vc-helpers>
function max(x: int, y: int): int
{
  if x > y then x else y
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int) returns (result: seq<int>)
  requires ValidInput(n, a, b)
  ensures ValidOutput(result, n, a, b)
// </vc-spec>
// <vc-code>
{
  var area := 6 * n;
  var dim1 := max(a, b);
  var dim2 := max(b, a);
  
  if dim1 * dim2 >= area {
    result := [dim1 * dim2, dim1, dim2];
  } else {
    var needed := area - dim1 * dim2;
    var extra := (needed + dim1 - 1) / dim1;
    dim2 := dim2 + extra;
    result := [dim1 * dim2, dim1, dim2];
  }
}
// </vc-code>
