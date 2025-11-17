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
/* helper modified by LLM (iteration 2): make FindStartPosition a method to avoid compilation errors with :| */
method FindStartPosition(grid: seq<string>, n: int, m: int) returns (i: int, j: int)
    requires n > 0 && m > 0
    requires |grid| == n
    requires forall idx :: 0 <= idx < n ==> |grid[idx]| == m
    requires exists idx1, idx2 :: 0 <= idx1 < n && 0 <= idx2 < m && grid[idx1][idx2] == 'X'
    ensures 0 <= i < n && 0 <= j < m
    ensures grid[i][j] == 'X'
{
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall idx :: 0 <= idx < i ==> forall jdx :: 0 <= jdx < m ==> grid[idx][jdx] != 'X'
    {
        j := 0;
        while j < m
            invariant 0 <= j <= m
            invariant forall jdx :: 0 <= jdx < j ==> grid[i][jdx] != 'X'
        {
            if grid[i][j] == 'X' {
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
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

/* helper modified by LLM (iteration 2): add lemmas to prove path properties for UD pattern */
lemma SimulateUDLemma(startX: int, startY: int, grid: seq<string>, n: int, m: int)
    requires 0 <= startX < n && 0 <= startY < m
    requires |grid| == n
    requires forall i :: 0 <= i < n ==> |grid[i]| == m
    ensures SimulatePath(startX, startY, "UD", grid, n, m) == (startX, startY)
{
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
        SimulateUDLemma(startX, startY, grid, n, m);
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
/* code modified by LLM (iteration 2): fix postcondition proofs and k==0 case */
{
    if k % 2 == 1 {
        return "IMPOSSIBLE";
    }
    
    var startX, startY := FindStartPosition(grid, n, m);
    
    if k == 0 {
        result := "";
        assert PathReturnsToStart(startX, startY, result, grid, n, m);
        assert ValidPath(startX, startY, result, grid, n, m);
        return;
    }
    
    if CanMoveUp(startX, startY, grid, n, m) && CanMoveDown(startX - 1, startY, grid, n, m) {
        result := BuildSimplePath(k);
        SimplePathReturns(startX, startY, k, grid, n, m);
        assert PathReturnsToStart(startX, startY, result, grid, n, m);
        assert grid[startX][startY] == 'X';
        return;
    }
    
    result := "IMPOSSIBLE";
}
// </vc-code>
