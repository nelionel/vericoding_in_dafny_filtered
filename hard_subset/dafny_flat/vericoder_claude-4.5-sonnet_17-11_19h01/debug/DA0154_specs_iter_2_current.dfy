// <vc-preamble>
function is_tandem_repeat(s: seq<char>): bool
{
    if |s| % 2 != 0 then false
    else
        var half_len := |s| / 2;
        var first_half := s[0..half_len];
        var second_half := s[half_len..];
        forall i :: 0 <= i < half_len ==> 
            (first_half[i] == '*' || second_half[i] == '*' || first_half[i] == second_half[i])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added lemma to help prove existential invariant */
lemma ExistentialPreservation(extended: seq<char>, i: int, old_result: int, new_result: int, max_len: int)
  requires 0 <= i < max_len
  requires old_result % 2 == 0
  requires new_result % 2 == 0
  requires new_result >= old_result
  requires old_result > 0 ==> exists idx, n :: 0 <= idx < i && 2 <= n <= max_len - idx && n % 2 == 0 && is_tandem_repeat(extended[idx..idx+n]) && n == old_result
  ensures new_result > 0 ==> exists idx, n :: 0 <= idx <= i && 2 <= n <= max_len - idx && n % 2 == 0 && is_tandem_repeat(extended[idx..idx+n]) && (n == old_result || n == new_result)
{
}
// </vc-helpers>

// <vc-spec>
method solve(s: string, k: int) returns (result: int)
    requires k >= 1
    requires |s| >= 1
    ensures result >= 0
    ensures result % 2 == 0
    ensures result <= |s| + k
    ensures forall i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 && 
            is_tandem_repeat((s + seq(k, j => '*'))[i..i+n]) ==> n <= result
    ensures result == 0 ==> forall i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 ==> 
            !is_tandem_repeat((s + seq(k, j => '*'))[i..i+n])
    ensures result > 0 ==> exists i, n :: 0 <= i < |s| + k && 2 <= n <= |s| + k - i && n % 2 == 0 && 
            (is_tandem_repeat((s + seq(k, j => '*'))[i..i+n]) && n == result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed loop invariants to maintain existential property */
  var extended := s + seq(k, j => '*');
  var max_len := |extended|;
  result := 0;
  
  var i := 0;
  while i < max_len
    invariant 0 <= i <= max_len
    invariant result >= 0
    invariant result % 2 == 0
    invariant result <= |s| + k
    invariant forall idx, n :: 0 <= idx < i && 2 <= n <= max_len - idx && n % 2 == 0 && 
              is_tandem_repeat(extended[idx..idx+n]) ==> n <= result
    invariant result > 0 ==> exists idx, n :: 0 <= idx < max_len && 2 <= n <= max_len - idx && n % 2 == 0 && 
              is_tandem_repeat(extended[idx..idx+n]) && n == result
  {
    var n := 2;
    while n <= max_len - i
      invariant 2 <= n
      invariant n % 2 == 0
      invariant result >= 0
      invariant result % 2 == 0
      invariant result <= |s| + k
      invariant forall idx, len :: 0 <= idx < i && 2 <= len <= max_len - idx && len % 2 == 0 && 
                is_tandem_repeat(extended[idx..idx+len]) ==> len <= result
      invariant forall len :: 2 <= len < n && len % 2 == 0 && i + len <= max_len &&
                is_tandem_repeat(extended[i..i+len]) ==> len <= result
      invariant result > 0 ==> exists idx, len :: 0 <= idx < max_len && 2 <= len <= max_len - idx && len % 2 == 0 && 
                is_tandem_repeat(extended[idx..idx+len]) && len == result
    {
      if i + n <= max_len && is_tandem_repeat(extended[i..i+n]) {
        if n > result {
          result := n;
        }
      }
      n := n + 2;
    }
    i := i + 1;
  }
}
// </vc-code>
