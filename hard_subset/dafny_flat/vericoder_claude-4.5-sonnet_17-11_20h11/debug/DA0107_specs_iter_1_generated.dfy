// <vc-preamble>
predicate ValidInput(pizzas: seq<int>) {
    forall i :: 0 <= i < |pizzas| ==> pizzas[i] >= 0
}

function validatePizzaSolution(pizzas: seq<int>, index: int, d: bool, p: int): bool
    requires 0 <= index <= |pizzas|
    requires p == 0 || p == 1
    decreases |pizzas| - index
{
    if index == |pizzas| then
        d && p == 0
    else
        var requirement := pizzas[index];
        var newP := if requirement % 2 == 1 then 1 - p else p;
        var newD := if requirement % 2 == 0 && p == 1 && requirement == 0 then false else d;
        validatePizzaSolution(pizzas, index + 1, newD, newP)
}

predicate CanFulfillRequirements(pizzas: seq<int>) {
    validatePizzaSolution(pizzas, 0, true, 0)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(pizzas: seq<int>) returns (result: string)
    requires ValidInput(pizzas)
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanFulfillRequirements(pizzas)
// </vc-spec>
// <vc-code>
{
  var index := 0;
  var d := true;
  var p := 0;
  
  while index < |pizzas|
    invariant 0 <= index <= |pizzas|
    invariant p == 0 || p == 1
    invariant validatePizzaSolution(pizzas, 0, true, 0) == validatePizzaSolution(pizzas, index, d, p)
  {
    var requirement := pizzas[index];
    var newP := if requirement % 2 == 1 then 1 - p else p;
    var newD := if requirement % 2 == 0 && p == 1 && requirement == 0 then false else d;
    p := newP;
    d := newD;
    index := index + 1;
  }
  
  if d && p == 0 {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>
