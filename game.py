
from typing import Any, NamedTuple, Protocol
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
    monsters: list[tuple[int,int]]
    chests: list[tuple[int,int]]

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

    chest_rooms = [(bv(i,'x'), bv(i,'y')) for i in range(len(puzzle.chests))]

    return SymbolicSolution(board, chest_rooms)  # type: ignore

