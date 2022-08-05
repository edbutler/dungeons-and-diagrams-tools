
from typing import Any, NamedTuple, Protocol
import z3
from graph import *

class Solver(Protocol):
    def add(self, *args:Any) -> None: ...

# true means a wall, false means an empty space
Cell = z3.BoolRef|bool

Location = tuple[z3.BitVecRef|int,z3.BitVecRef|int]

BoardSize = 8

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

one = z3.BitVecVal(1, 4)
zero = z3.BitVecVal(0, 4)

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
        return z3.BitVec(f'chest-room-{i}-{name}', 4)

    chest_rooms = [(bv(i,'x'), bv(i,'y')) for i in range(len(puzzle.chests))]

    return SymbolicSolution(board, chest_rooms)  # type: ignore

def num_filled(cells:list[z3.BoolRef|bool]):
    return z3.Sum(*[z3.If(x, one, zero) for x in cells])

def neighbors_of(x:int, y:int):
    return [(x+1,y),(x-1,y),(x,y+1),(x,y-1)]

def is_corner_of_treaure_room(room:Location, x:int, y:int):
    rx = room[0]
    ry = room[1]
    return z3.And(x == rx, y == ry)

def is_cell_in_treaure_room(room:Location, x:int, y:int):
    rx = room[0]
    ry = room[1]
    return z3.And(
        z3.Or(x == rx, x - 1 == rx, x - 2 == rx),
        z3.Or(y == ry, y - 1 == ry, y - 2 == ry))

def is_square_in_treaure_room(room:Location, sx:int, sy:int):
    rx = room[0]
    ry = room[1]
    return z3.And(
        z3.Or(sx == rx, sx - 1 == rx),
        z3.Or(sy == ry, sy - 1 == ry))

def add_constrants(solver:Solver, puzzle:Puzzle, soln:SymbolicSolution):
    # row/col filled counts
    for i in range(BoardSize):
        row = row_ref(soln, i)
        total = puzzle.rows[i]
        solver.add(total == num_filled(row))

    for j in range(BoardSize):
        col = col_ref(soln, j)
        total = puzzle.cols[j]
        solver.add(total == num_filled(col))

    # chests always in the treasure rooms, and rooms are always empty
    for i in range(BoardSize):
        for j in range(BoardSize):
            is_in_any_treausre_room = z3.Or(*[is_cell_in_treaure_room(t, i, j) for t in soln.chest_rooms])
            solver.add(z3.Implies(is_in_any_treausre_room, z3.Not(cell_ref(soln, i, j))))

            if (i,j) in puzzle.chests:
                solver.add(is_in_any_treausre_room)

    # treasure rooms always have exactly one exit
    for i in range(BoardSize):
        for j in range(BoardSize):
            is_in_any_treausre_room = z3.Or(*[is_corner_of_treaure_room(t, i, j) for t in soln.chest_rooms])

            # only one of the surrounding cells can be empty
            walls = [
                (i-1,j), (i-1,j+1), (i-1,j+2),
                (i+3,j), (i+3,j+1), (i+3,j+2),
                (i,j-1), (i+1,j-1), (i+2, j-1),
                (i,j+3), (i+1,j+3), (i+2, j+3) ]

            solver.add(
                z3.Implies(
                    is_in_any_treausre_room,
                    11 == num_filled([cell_ref_or_true(soln,x,y) for x,y in walls])))

    # monsters always at a dead end
    for mx, my in puzzle.monsters:
        solver.add(z3.Not(cell_ref(soln, mx, my)))
        neighbors = neighbors_of(mx,my)
        solver.add(3 == num_filled([cell_ref_or_true(soln,x,y) for x,y in neighbors]))

    # no empty 2x2 squares except in treasure rooms
    for i in range(BoardSize - 1):
        for j in range(BoardSize - 1):
            cells = [(i,j), (i+1,j), (i,j+1), (i+1,j+1)]

            is_in_any_treausre_room = z3.Or(*[is_square_in_treaure_room(t, i, j) for t in soln.chest_rooms])

            # every 2x2 square is either wholly in a treasure room or has at least one filled cell
            solver.add(
                z3.Or(
                    is_in_any_treausre_room,
                    1 <= num_filled([cell_ref(soln,x,y) for x,y in cells])))

    # no dead ends except near monsters
    for i in range(BoardSize):
        for j in range(BoardSize):
            if (i,j) not in puzzle.monsters:
                neighbors = neighbors_of(i,j)
                # every cell is either filled or has at least 2 empty neighbors
                solver.add(
                    z3.Or(
                        cell_ref(soln,i,j),
                        2 >= num_filled([cell_ref_or_true(soln,x,y) for x,y in neighbors])))

    # all open spaces must be connected
    all_cell_indices = [(x,y) for x in range(BoardSize) for y in range(BoardSize)]
    cell_to_flat_index = {(x,y):i for i, (x,y) in enumerate(all_cell_indices)}
    # a cell is a node in the graph if it's empty (i.e., if it's false)
    nodes = [z3.Not(cell_ref_t(soln, cell)) for cell in all_cell_indices]
    edges = [
        (cell_to_flat_index[(x,y)], cell_to_flat_index[(a,b)])
            for x in range(BoardSize)
            for y in range(BoardSize)
            for (a,b) in [(x,y+1), (x+1,y)]
            if a < BoardSize and b < BoardSize]
    # duplicate the entire edge list to represent both directions since the constraints are for directed graphs
    edges = edges + [(b,a) for (a,b) in edges]
    assert_connected(solver, nodes, edges)

