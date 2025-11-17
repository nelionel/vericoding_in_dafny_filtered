// <vc-preamble>
predicate validInput(input: string)
reads *
requires |input| > 0
requires exists i :: 0 <= i < |input| && input[i] == '\n'
{
    var parts := parseInput(input);
    |parts| == 5 &&
    parts[0] >= 4 && parts[0] <= 100 &&
    parts[1] >= 1 && parts[1] <= parts[0] &&
    parts[2] >= 1 && parts[2] <= parts[0] &&
    parts[3] >= 1 && parts[3] <= parts[0] &&
    parts[4] >= 1 && parts[4] <= parts[0] &&
    parts[1] != parts[2] && parts[1] != parts[3] && parts[1] != parts[4] &&
    parts[2] != parts[3] && parts[2] != parts[4] &&
    parts[3] != parts[4]
}

predicate trainsWillMeet(input: string)
reads *
requires |input| > 0
requires exists i :: 0 <= i < |input| && input[i] == '\n'
requires validInput(input)
{
    var parts := parseInput(input);
    var n := parts[0];
    var a := parts[1];
    var x := parts[2];
    var b := parts[3]; 
    var y := parts[4];

    if a == b then true
    else simulateTrains(n, a, x, b, y)
}

function simulateTrains(n: int, a: int, x: int, b: int, y: int): bool
requires n >= 4 && 1 <= a <= n && 1 <= x <= n && 1 <= b <= n && 1 <= y <= n
requires a != x && a != b && a != y && x != b && x != y && b != y
decreases 2 * n
{
    simulateTrainsHelper(n, a, x, b, y, 2 * n)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added reads clause to ParseIntegers and fixed preconditions in simulateTrainsHelper */
function parseInput(input: string): seq<int>
reads *
requires |input| > 0
requires exists i :: 0 <= i < |input| && input[i] == '\n'
{
  var newlineIndex := FindNewline(input, 0);
  if newlineIndex >= 0 then
    ParseIntegers(input[..newlineIndex])
  else
    []
}

function FindNewline(s: string, start: int): int
reads *
requires 0 <= start <= |s|
ensures -1 <= FindNewline(s, start) < |s|
ensures FindNewline(s, start) >= 0 ==> start <= FindNewline(s, start) < |s| && s[FindNewline(s, start)] == '\n'
ensures FindNewline(s, start) == -1 ==> forall i :: start <= i < |s| ==> s[i] != '\n'
decreases |s| - start
{
  if start >= |s| then -1
  else if s[start] == '\n' then start
  else FindNewline(s, start + 1)
}

function ParseIntegers(s: string): seq<int>
reads *
{
  if |s| == 0 then []
  else
    var parts := SplitOnSpaces(s);
    seq(|parts|, i requires 0 <= i < |parts| reads * => ParseInt(parts[i]))
}

function SplitOnSpaces(s: string): seq<string>
reads *
{
  SplitOnSpacesHelper(s, 0, "")
}

function SplitOnSpacesHelper(s: string, pos: int, current: string): seq<string>
reads *
requires 0 <= pos <= |s|
decreases |s| - pos
{
  if pos >= |s| then
    if |current| > 0 then [current] else []
  else if s[pos] == ' ' then
    if |current| > 0 then [current] + SplitOnSpacesHelper(s, pos + 1, "")
    else SplitOnSpacesHelper(s, pos + 1, "")
  else
    SplitOnSpacesHelper(s, pos + 1, current + [s[pos]])
}

function ParseInt(s: string): int
reads *
{
  if |s| == 0 then 0
  else if s[0] == '-' then -ParseUInt(s[1..])
  else ParseUInt(s)
}

function ParseUInt(s: string): int
reads *
decreases |s|
{
  if |s| == 0 then 0
  else if |s| == 1 then DigitToInt(s[0])
  else ParseUInt(s[..|s|-1]) * 10 + DigitToInt(s[|s|-1])
}

function DigitToInt(c: char): int
{
  if '0' <= c <= '9' then (c as int) - ('0' as int)
  else 0
}

function simulateTrainsHelper(n: int, a: int, x: int, b: int, y: int, fuel: int): bool
requires n >= 4 && 1 <= a <= n && 1 <= x <= n && 1 <= b <= n && 1 <= y <= n
requires a != x && a != b && a != y && x != b && x != y && b != y
requires fuel >= 0
decreases fuel
{
  if fuel == 0 then false
  else if a == b then true
  else
    var next_a := if a == n then 1 else a + 1;
    var next_b := if b == 1 then n else b - 1;
    if next_a == x && next_b == y then false
    else if next_a == next_b then true
    else if next_a == x || next_a == b || next_a == y || next_b == x || next_b == b || next_b == y then false
    else simulateTrainsHelper(n, next_a, x, next_b, y, fuel - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
requires |stdin_input| > 0
requires exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n'
requires validInput(stdin_input)
ensures result == "YES\n" || result == "NO\n"
ensures result == "YES\n" <==> trainsWillMeet(stdin_input)
ensures result == "NO\n" <==> !trainsWillMeet(stdin_input)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): parse input and call simulateTrains */
  var parts := parseInput(stdin_input);
  var n := parts[0];
  var a := parts[1];
  var x := parts[2];
  var b := parts[3];
  var y := parts[4];
  
  if a == b {
    result := "YES\n";
  } else {
    var willMeet := simulateTrains(n, a, x, b, y);
    if willMeet {
      result := "YES\n";
    } else {
      result := "NO\n";
    }
  }
}
// </vc-code>
