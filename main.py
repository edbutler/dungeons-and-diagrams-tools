from solve import *
from game import *

def test(p:Puzzle):
    soln = solve(p)
    if soln is not None:
        print_solution(p, soln)

p = Puzzle(
    # the numer of filled blocks for each row
    rows=[2,1,4,4,2,5,2,4],
    # the numer of filled blocks for each column
    cols=[1,3,3,3,3,5,3,3],
    # the 0-indexed x,y location of each monster in the grid
    monsters=boolean_grid_from_tuples([(7,0),(7,4),(6,5),(7,6)]),
    # the 0-indexed x,y location of each chest in the grid
    chests=boolean_grid_from_tuples([(0,0)]))

test(p)