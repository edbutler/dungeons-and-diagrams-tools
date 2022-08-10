
from game import *
from rules import add_constraints
import z3

def solve(p:SymbolicPuzzle|ConcretePuzzle):
    """assuming p is a valid puzzle, this returns the solution to p."""

    s = z3.Solver()
    b = make_solution_guess(p)

    add_constraints(s, p, b)

    if s.check() == z3.sat:
        #print(s.statistics())
        m = s.model()
        return b.evaluate(p, m)
    else:
        print("Unsolvable!")

def verify(p:SymbolicPuzzle|ConcretePuzzle):
    """verifies that p is a valid puzzle, returning the solution if it exists.
    Unlike `solve`, this checks that the solution is unique."""

    s = z3.Solver()
    b = make_solution_guess(p)
    add_constraints(s, p, b)

    # first make sure it has any solution at all
    if s.check() != z3.sat:
        print('puzzle has no solution!')
        return None

    # and cache this solution before the next check since extra clauses mess up the model
    m = s.model()
    soln = b.evaluate(p, m)

    # then ensure the solution is unique by looking for a second one
    b2 = make_solution_guess(p)
    add_constraints(s, p, b2)

    # solutions must differ somewhere
    s.add(z3.Or(*[b.board[x][y] != b2.board[x][y] for x in range(BoardSize) for y in range(BoardSize)]))

    # if this is sat, then we have 2 solutions, so it's an invalid puzzle
    if s.check() == z3.sat:
        print('solution is not unique!')
        return None

    return soln

def print_solution(soln:ConcreteSolution):
    p = soln.puzzle
    print("solution:")
    print(f"  {''.join([str(x) for x in p.cols])} ")
    print("  -------- ")
    for y in range(BoardSize):
        print(f'{p.rows[y]}|', end="")
        for x in range(BoardSize):
            if p.monsters[x][y]:
                c = "M"
            elif p.chests[x][y]:
                c = "T"
            elif soln.board[x][y]:
                c = "█"
            else:
                c = " "
            print(c, end="")
        print("|")
    print("  -------- \n")
