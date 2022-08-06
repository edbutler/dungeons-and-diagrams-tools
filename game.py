
from typing import NamedTuple
import math
import z3

# true means a wall, false means an empty space
Cell = z3.BoolRef|bool

Location = tuple[z3.BitVecRef|int,z3.BitVecRef|int]

BoardSize = 8
BitvecBits = math.ceil(math.log2(BoardSize+1))

class SymbolicSolution(NamedTuple):
    #stored column major, so indexing is x (col) then y (row)
    board: list[list[Cell]]
    # the top-left (lowest indexed) corner of each chest room
    chest_rooms: list[Location]

class ConcreteSolution(NamedTuple):
    #stored column major, so indexing is x (col) then y (row)
    board: list[list[bool]]

class Puzzle(NamedTuple):
    rows: list[int]
    cols: list[int]
    # stored column major like the board
    monsters: list[list[Cell]]
    chests: list[list[Cell]]

def boolean_grid_from_tuples(tuples:list[tuple[int,int]]) -> list[list[Cell]]:
    return [[(x,y) in tuples for y in range(BoardSize)] for x in range(BoardSize)]

one = z3.BitVecVal(1, BitvecBits)
zero = z3.BitVecVal(0, BitvecBits)

def cell_ref(s:SymbolicSolution, x:int, y:int):
    return s.board[x][y];

def cell_ref_t(s:SymbolicSolution, cell:tuple[int, int]):
    return cell_ref(s, cell[0], cell[1])

def cell_ref_or_true(s:SymbolicSolution, x:int, y:int):
    if x >= 0 and x < BoardSize and y >= 0 and y < BoardSize:
        return cell_ref(s, x, y)
    else:
        return z3.BoolVal(True)

def row_ref(s:SymbolicSolution, row_y:int):
    return [c[row_y] for c in s.board]

def col_ref(s:SymbolicSolution, col_x:int):
    return s.board[col_x]

def make_solution_guess(puzzle:Puzzle) -> SymbolicSolution:
    def make_cell(x,y):
        return z3.Bool(f'cell-{x}-{y}')
    board = [[make_cell(x,y) for y in range(BoardSize)] for x in range(BoardSize)]

    def bv(i:int,name:str):
        return z3.BitVec(f'chest-room-{i}-{name}', BitvecBits)

    # this is hardcoded for 8x8 puzzles, but could make it based on size
    max_chests = 4

    # we don't need to worry about making too many of these for the number of chests
    # since they can overlap with each other (we don't even need to handle the zero
    # chest case; the solver will place these rooms off the grid).
    # we just need to make sure there are *at least* as many vars here as chests.
    chest_rooms = [(bv(i,'x'), bv(i,'y')) for i in range(max_chests)]

    return SymbolicSolution(board, chest_rooms)  # type: ignore

