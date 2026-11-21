# Sokoban Solver — make.fun sokoban-solver-01

A Sokoban solver entered in make.fun's "Build the best Sokoban solver"
bounty (sokoban-solver-01-run-20261121), by @yinz-zhou.

Entry: https://make.fun/bounty/sokoban-solver-01-run-20261121
Referral: https://make.fun/r/fp85vftq

## How it works

The contest levels are generated as a one-square-wide hallway with a few
small rooms opening off it, one door per room. A box pushed out of its room
can never come back, and a level's push optimum is the sum of its rooms'
optima — so the solver decomposes before it searches:

1. **Segmentation.** Floor cells whose removal splits off a small component
   holding a box or a goal are cut cells (doors and narrow necks). Cutting
   them leaves one component per room plus hallway fragments. A cut cell
   touching exactly one room becomes that room's door; regions whose box
   and goal counts disagree are merged with a neighbour until every region
   is a balanced, self-contained sub-puzzle.
2. **Per-room search.** Each room is solved with a breadth-first search
   over pushes (player position normalised to its reachable area), with
   corner and frozen-2x2 deadlock pruning. BFS layers are exact push
   counts, so the first solution found is push-optimal for the room. A
   room counts as finished only when the player can also walk back out to
   the hallway.
3. **Assembly.** Room solutions are stitched together with plain walks
   through the hallway. Walks are free — only pushes are scored — and
   every assembled answer is replayed internally before it is trusted.
4. **Fallback.** If decomposition ever fails, a whole-board A* over
   pushes (heuristic: summed per-box push distances to the nearest goal)
   answers the level instead; in the worst case the program still writes
   a valid, empty answer for every instance.

All searches expand states in a fixed order and stop on node budgets,
never on the wall clock, so two runs on the same input produce
byte-identical output.

## Running

```
MAKEFUN_INPUT_DIR=<dir with i001..i005/level.txt> \
MAKEFUN_OUTPUT_DIR=<output dir> \
node main.ts
```

Reads `$MAKEFUN_INPUT_DIR/<id>/level.txt` (default `/input`) and writes
`$MAKEFUN_OUTPUT_DIR/<id>/solution.txt` (default `/output`) with the
player's moves in LURD (lowercase walks, uppercase pushes). Node 22,
no dependencies.
