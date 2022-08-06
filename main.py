from typing import Callable
from solve import *
from game import *

def maybe_print(soln:ConcreteSolution|None):
    if soln is not None:
        print_solution(soln)

example_puzzle = ConcretePuzzle(
    # the numer of filled blocks for each row
    rows=[2,1,4,4,2,5,2,4],
    # the numer of filled blocks for each column
    cols=[1,3,3,3,3,5,3,3],
    # the 0-indexed x,y location of each monster in the grid
    monsters=boolean_grid_from_tuples([(7,0),(7,4),(6,5),(7,6)]),
    # the 0-indexed x,y location of each chest in the grid
    chests=boolean_grid_from_tuples([(0,0)]))

# can solve puzzles
print('solving...')
maybe_print(solve(example_puzzle))

# can verify that puzzles have unique solutions
print('verifying...')
maybe_print(verify(example_puzzle))

# can even solve puzzles where parts of the puzzle are undefined
print('solving with some of the rows/cols unconstrained...')
partial_puzzle = SymbolicPuzzle(
    # `symbolic_int` is any integer value, the solver needs to figure out what it should be
    rows=[2,1,symbolic_int('A'),4,2,symbolic_int('B'),2,4],
    cols=[symbolic_int('C'),3,3,3,3,5,3,symbolic_int('D')],
    monsters=boolean_grid_from_tuples([(7,0),(7,4),(6,5),(7,6)]), # type: ignore
    chests=boolean_grid_from_tuples([(0,0)])) # type: ignore

maybe_print(solve(partial_puzzle))