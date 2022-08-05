
from game import *
import z3

def solve(p:Puzzle):
    s = z3.Solver()
    b = make_solution_guess(p)

    add_constrants(s, p, b)

    if s.check() == z3.sat:
        #print(s.statistics())
        m = s.model()
        return ConcreteSolution([[m.evaluate(x, True) for x in col] for col in b.board])
    else:
        print("Unsolvable!")

def print_solution(p:Puzzle, soln:ConcreteSolution):
    print("solution:")
    print(f"  {''.join([str(x) for x in p.cols])} ")
    print("  -------- ")
    for y in range(BoardSize):
        print(f'{p.rows[y]}|', end="")
        for x in range(BoardSize):
            if (x,y) in p.monsters:
                c = "M"
            elif (x,y) in p.chests:
                c = "T"
            elif soln.board[x][y]:
                c = "█"
            else:
                c = " "
            print(c, end="")
        print("|")
    print("  -------- \n")
