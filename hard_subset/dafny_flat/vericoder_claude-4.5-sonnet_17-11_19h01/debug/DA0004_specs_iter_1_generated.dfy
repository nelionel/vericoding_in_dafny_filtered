// <vc-preamble>
predicate is_s_palindrome(s: string)
{
    var pal := "AHIMOoTUVvWwXxY";

    forall i :: 0 <= i < |s| ==> 
        var j := |s| - 1 - i;
        if i >= j then true
        else
            if s[i] == s[j] then s[i] in pal
            else (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
                 (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b')
}
// </vc-preamble>

// <vc-helpers>
predicate is_mirror_char(c: char, d: char)
{
  var pal := "AHIMOoTUVvWwXxY";
  (c == d && c in pal) ||
  (c == 'p' && d == 'q') || (c == 'q' && d == 'p') ||
  (c == 'b' && d == 'd') || (c == 'd' && d == 'b')
}

lemma is_s_palindrome_equiv(s: string)
  ensures is_s_palindrome(s) <==> (forall i :: 0 <= i < |s| / 2 ==> is_mirror_char(s[i], s[|s| - 1 - i]))
{
  if forall i :: 0 <= i < |s| / 2 ==> is_mirror_char(s[i], s[|s| - 1 - i]) {
    assert forall i :: 0 <= i < |s| ==> 
      var j := |s| - 1 - i;
      if i >= j then true
      else is_mirror_char(s[i], s[j]);
  }
  if is_s_palindrome(s) {
    assert forall i :: 0 <= i < |s| / 2 ==> is_mirror_char(s[i], s[|s| - 1 - i]);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| >= 1
    ensures result == "TAK" || result == "NIE"
    ensures result == "TAK" <==> is_s_palindrome(s)
// </vc-spec>
// <vc-code>
{
  var pal := "AHIMOoTUVvWwXxY";
  var is_pal := true;
  var i := 0;
  while i < |s| / 2
    invariant 0 <= i <= |s| / 2
    invariant is_pal <==> (forall k :: 0 <= k < i ==> is_mirror_char(s[k], s[|s| - 1 - k]))
  {
    var j := |s| - 1 - i;
    var match := false;
    if s[i] == s[j] && s[i] in pal {
      match := true;
    } else if (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') {
      match := true;
    } else if (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b') {
      match := true;
    }
    if !match {
      is_pal := false;
    }
    i := i + 1;
  }
  is_s_palindrome_equiv(s);
  if is_pal {
    result := "TAK";
  } else {
    result := "NIE";
  }
}
// </vc-code>
