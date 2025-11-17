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
/* helper modified by LLM (iteration 3): fixed splitOnSpaces to handle empty slices and added decreases clause to findSpace */
function parseInput(input: string): seq<int>
reads *
requires |input| > 0
requires exists i :: 0 <= i < |input| && input[i] == '\n'
{
  var parts := splitOnSpaces(input);
  if |parts| >= 5 then
    [stringToInt(parts[0]), stringToInt(parts[1]), stringToInt(parts[2]), stringToInt(parts[3]), stringToInt(parts[4])]
  else
    []
}

function splitOnSpaces(s: string): seq<string>
reads *
{
  if |s| == 0 then []
  else
    var idx := findSpace(s, 0);
    if idx < 0 then [s]
    else if idx == 0 then splitOnSpaces(s[1..])
    else [s[..idx]] + splitOnSpaces(s[idx+1..])
}

function findSpace(s: string, start: int): int
reads *
requires 0 <= start <= |s|
decreases |s| - start
{
  if start >= |s| then -1
  else if s[start] == ' ' || s[start] == '\n' then start
  else findSpace(s, start + 1)
}

function stringToInt(s: string): int
reads *
{
  if |s| == 0 then 0
  else if |s| == 1 then charToDigit(s[0])
  else stringToInt(s[..|s|-1]) * 10 + charToDigit(s[|s|-1])
}

function charToDigit(c: char): int
{
  if '0' <= c <= '9' then (c as int) - ('0' as int)
  else 0
}

function nextPosition(pos: int, n: int, forward: bool): int
requires n >= 4 && 1 <= pos <= n
ensures 1 <= nextPosition(pos, n, forward) <= n
{
  if forward then
    if pos == n then 1 else pos + 1
  else
    if pos == 1 then n else pos - 1
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
    var nextA := nextPosition(a, n, true);
    var nextB := nextPosition(b, n, false);
    if nextA == x && nextB == y then false
    else if nextA == nextB then true
    else if nextA != x && nextA != b && nextA != y && x != nextB && x != y && nextB != y then
      simulateTrainsHelper(n, nextA, x, nextB, y, fuel - 1)
    else false
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
/* code modified by LLM (iteration 3): same implementation as iteration 2 */
{
  var parts := parseInput(stdin_input);
  var n := parts[0];
  var a := parts[1];
  var x := parts[2];
  var b := parts[3];
  var y := parts[4];
  
  if a == b {
    result := "YES\n";
  } else {
    var meet := simulateTrains(n, a, x, b, y);
    if meet {
      result := "YES\n";
    } else {
      result := "NO\n";
    }
  }
}
// </vc-code>
