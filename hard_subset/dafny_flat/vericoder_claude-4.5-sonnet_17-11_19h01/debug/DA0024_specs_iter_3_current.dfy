// <vc-preamble>
function power(base: int, exp: int): int
    requires exp >= 0
    ensures exp == 0 ==> power(base, exp) == 1
    ensures base > 0 ==> power(base, exp) > 0
    ensures base != 0 ==> power(base, exp) != 0
    decreases exp
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): removed gcd and lcm to avoid timeouts, use direct computation */
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires n > 0 && k >= 0
    ensures result > 0
    ensures result % n == 0
    ensures result % power(10, k) == 0
    ensures forall m :: m > 0 && m % n == 0 && m % power(10, k) == 0 ==> result <= m
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute LCM directly using division properties */
  var tenPowK := power(10, k);
  var g := n;
  var temp := tenPowK;
  
  while temp > 0
    invariant g > 0
    invariant temp >= 0
    decreases temp
  {
    var r := g % temp;
    g := temp;
    temp := r;
  }
  
  result := (n * tenPowK) / g;
}
// </vc-code>
