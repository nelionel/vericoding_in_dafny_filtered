// <vc-preamble>
predicate ValidInput(n: int, m: int, k: int, grid: seq<string>)
{
    n > 0 && m > 0 && k >= 0 &&
    |grid| == n &&
    (forall i :: 0 <= i < n ==> |grid[i]| == m) &&
    (exists i, j :: 0 <= i < n && 0 <= j < m && grid[i][j] == 'X') &&
    (forall i :: 0 <= i < n ==> forall c :: c in grid[i] ==> c == '.' || c == '*' || c == 'X') &&
    |set i,j | 0 <= i < n && 0 <= j < m && grid[i][j] == 'X' :: (i,j)| == 1
}

function GetNextPosition(x: int, y: int, move: char): (int, int)
{
    match move
        case 'D' => (x + 1, y)
        case 'L' => (x, y - 1)
        case 'R' => (x, y + 1)
        case 'U' => (x - 1, y)
        case _ => (x, y)
}

function SimulatePath(startX: int, startY: int, path: string, grid: seq<string>, n: int, m: int): (int, int)
    decreases |path|
{
    if |path| == 0 then (startX, startY)
    else 
        var nextPos := GetNextPosition(startX, startY, path[0]);
        SimulatePath(nextPos.0, nextPos.1, path[1..], grid, n, m)
}

predicate ValidPath(startX: int, startY: int, path: string, grid: seq<string>, n: int, m: int)
{
    forall i :: 0 <= i <= |path| ==> 
        var pos := SimulatePath(startX, startY, path[..i], grid, n, m);
        0 <= pos.0 < n && 0 <= pos.1 < m && 
        pos.0 < |grid| && pos.1 < |grid[pos.0]| &&
        grid[pos.0][pos.1] != '*'
}

predicate PathReturnsToStart(startX: int, startY: int, path: string, grid: seq<string>, n: int, m: int)
{
    var finalPos := SimulatePath(startX, startY, path, grid, n, m);
    finalPos.0 == startX && finalPos.1 == startY
}

predicate ValidDirections(path: string)
{
    forall c :: c in path ==> c == 'D' || c == 'L' || c == 'R' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
function FindStartPosition(grid: seq<string>, n: int, m: int): (int, int)
    requires n > 0 && m > 0
    requires |grid| == n
    requires forall i :: 0 <= i < n ==> |grid[i]| == m
    requires exists i, j :: 0 <= i < n && 0 <= j < m && grid[i][j] == 'X'
{
    var i :| 0 <= i < n && exists j :: 0 <= j < m && grid[i][j] == 'X';
    var j :| 0 <= j < m && grid[i][j] == 'X';
    (i, j)
}

function BuildSimplePath(k: int): string
    requires k >= 0 && k % 2 == 0
    ensures |BuildSimplePath(k)| == k
    ensures ValidDirections(BuildSimplePath(k))
{
    if k == 0 then ""
    else if k == 2 then "UD"
    else "UD" + BuildSimplePath(k - 2)
}

lemma SimplePathReturns(startX: int, startY: int, k: int, grid: seq<string>, n: int, m: int)
    requires k >= 0 && k % 2 == 0
    requires 0 <= startX < n && 0 <= startY < m
    requires |grid| == n
    requires forall i :: 0 <= i < n ==> |grid[i]| == m
    ensures PathReturnsToStart(startX, startY, BuildSimplePath(k), grid, n, m)
    decreases k
{
    if k == 0 {
    } else if k == 2 {
    } else {
        SimplePathReturns(startX, startY, k - 2, grid, n, m);
    }
}

predicate CanMoveUp(x: int, y: int, grid: seq<string>, n: int, m: int)
{
    x - 1 >= 0 && x - 1 < n && y >= 0 && y < m && 
    x - 1 < |grid| && y < |grid[x - 1]| &&
    grid[x - 1][y] != '*'
}

predicate CanMoveDown(x: int, y: int, grid: seq<string>, n: int, m: int)
{
    x + 1 >= 0 && x + 1 < n && y >= 0 && y < m &&
    x + 1 < |grid| && y < |grid[x + 1]| &&
    grid[x + 1][y] != '*'
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int, grid: seq<string>) returns (result: string)
    requires ValidInput(n, m, k, grid)
    ensures k % 2 == 1 ==> result == "IMPOSSIBLE"
    ensures k % 2 == 0 ==> (
        result == "IMPOSSIBLE" || 
        (|result| == k && ValidDirections(result))
    )
    ensures result != "IMPOSSIBLE" ==> |result| == k
    ensures result != "IMPOSSIBLE" ==> (
        exists startX, startY :: 0 <= startX < n && 0 <= startY < m && 
        grid[startX][startY] == 'X' &&
        PathReturnsToStart(startX, startY, result, grid, n, m)
    )
    ensures result != "IMPOSSIBLE" ==> (
        exists startX, startY :: 0 <= startX < n && 0 <= startY < m && 
        grid[startX][startY] == 'X' &&
        ValidPath(startX, startY, result, grid, n, m)
    )
// </vc-spec>
// <vc-code>
{
    if k % 2 == 1 {
        return "IMPOSSIBLE";
    }
    
    var start := FindStartPosition(grid, n, m);
    var startX := start.0;
    var startY := start.1;
    
    if k == 0 {
        result := "";
        return;
    }
    
    if CanMoveUp(startX, startY, grid, n, m) && CanMoveDown(startX - 1, startY, grid, n, m) {
        result := BuildSimplePath(k);
        SimplePathReturns(startX, startY, k, grid, n, m);
        return;
    }
    
    result := "IMPOSSIBLE";
}
// </vc-code>
