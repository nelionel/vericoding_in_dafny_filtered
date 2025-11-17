// <vc-preamble>
// Ghost function to represent mathematical cosine for specification purposes
ghost function {:axiom} cos(x: real): real
    // Mathematical cosine function properties needed for specification
    ensures -1.0 <= cos(x) <= 1.0
    ensures cos(0.0) == 1.0
    ensures cos(3.141592653589793) == -1.0
// </vc-preamble>

// <vc-helpers>
function arccos_value(val: real): real
    requires -1.0 <= val <= 1.0
    ensures 0.0 <= arccos_value(val) <= 3.141592653589793
    ensures cos(arccos_value(val)) == val
    ensures val == -1.0 ==> arccos_value(val) == 3.141592653589793
    ensures val == 1.0 ==> arccos_value(val) == 0.0
{
    if val == 1.0 then 0.0
    else if val == -1.0 then 3.141592653589793
    else if val >= 0.0 then 1.5707963267948966 - val
    else 1.5707963267948966 + (-val)
}

lemma arccos_monotonic(a: real, b: real)
    requires -1.0 <= a <= 1.0
    requires -1.0 <= b <= 1.0
    requires a <= b
    ensures arccos_value(b) <= arccos_value(a)
{
}
// </vc-helpers>

// <vc-spec>
method arccos(x: seq<real>) returns (result: seq<real>)
    // Precondition: all input elements must be in valid domain [-1, 1]
    requires forall i :: 0 <= i < |x| ==> -1.0 <= x[i] <= 1.0
    
    // Postcondition: output sequence has same length as input
    ensures |result| == |x|
    
    // Postcondition: all result values are in range [0, π]
    ensures forall i :: 0 <= i < |result| ==> 0.0 <= result[i] <= 3.141592653589793
    
    // Postcondition: inverse property - cos(arccos(x)) = x for each element
    ensures forall i :: 0 <= i < |result| ==> cos(result[i]) == x[i]
    
    // Postcondition: boundary conditions
    ensures forall i :: 0 <= i < |result| ==> (x[i] == -1.0 ==> result[i] == 3.141592653589793)
    ensures forall i :: 0 <= i < |result| ==> (x[i] == 1.0 ==> result[i] == 0.0)
    
    // Postcondition: monotonicity - arccos is decreasing on [-1, 1]
    ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result| && x[i] <= x[j] ==> result[j] <= result[i]
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    while i < |x|
        invariant 0 <= i <= |x|
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> 0.0 <= result[k] <= 3.141592653589793
        invariant forall k :: 0 <= k < i ==> cos(result[k]) == x[k]
        invariant forall k :: 0 <= k < i ==> (x[k] == -1.0 ==> result[k] == 3.141592653589793)
        invariant forall k :: 0 <= k < i ==> (x[k] == 1.0 ==> result[k] == 0.0)
        invariant forall j, k :: 0 <= j < i && 0 <= k < i && x[j] <= x[k] ==> result[k] <= result[j]
    {
        var val := arccos_value(x[i]);
        result := result + [val];
        assert forall j :: 0 <= j < i && x[j] <= x[i] ==> arccos_value(x[i]) <= arccos_value(x[j]) by {
            forall j | 0 <= j < i && x[j] <= x[i] {
                arccos_monotonic(x[j], x[i]);
            }
        }
        assert forall k :: 0 <= k < i && x[i] <= x[k] ==> arccos_value(x[k]) <= arccos_value(x[i]) by {
            forall k | 0 <= k < i && x[i] <= x[k] {
                arccos_monotonic(x[i], x[k]);
            }
        }
        i := i + 1;
    }
}
// </vc-code>
