from solve import solve, print_solution
from game import Puzzle

def test(p:Puzzle):
    soln = solve(p)
    if soln is not None:
        print_solution(p, soln)

p = Puzzle(
    rows=[2,1,4,4,2,5,2,4],
    cols=[1,3,3,3,3,5,3,3],
    monsters=[(7,0),(7,4),(6,5),(7,6)],
    chests=[(0,0)])

test(p)