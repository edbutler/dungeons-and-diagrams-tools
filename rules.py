
from typing import Any, Protocol
import math
import z3
import itertools
from game import *

class Solver(Protocol):
    def add(self, *args:Any) -> None: ...

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

def add_constraints(solver:Solver, puzzle:Puzzle, soln:SymbolicSolution):
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

            is_chest = puzzle.chests[i][j]
            solver.add(z3.Implies(is_chest, is_in_any_treausre_room))

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
    for mx in range(BoardSize):
        for my in range(BoardSize):
            is_monster = puzzle.monsters[mx][my]
            solver.add(z3.Implies(is_monster, z3.Not(cell_ref(soln, mx, my))))
            neighbors = neighbors_of(mx,my)
            solver.add(z3.Implies(is_monster, 3 == num_filled([cell_ref_or_true(soln,x,y) for x,y in neighbors])))

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
            is_not_monster = z3.Not(puzzle.monsters[i][j])
            neighbors = neighbors_of(i,j)
            # every cell is either filled or has at least 2 empty neighbors
            solver.add(
                z3.Implies(
                    is_not_monster,
                    z3.Or(
                        cell_ref(soln,i,j),
                        2 >= num_filled([cell_ref_or_true(soln,x,y) for x,y in neighbors]))))

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

def assert_connected(
        solver:Solver,
        # the set of nodes in the graph, represented as symbolic booleans for whether they are actually in the graph
        potential_nodes:list[z3.BoolRef|z3.Probe],
        # assumes directed graph, so undirected edges must show up here twice
        edges: list[tuple[int,int]]):

    bits = math.ceil(math.log2(len(potential_nodes)))

    # we choose one node to be the source, and distances represents the minimal distance
    # to each node from the source. used_edge indicates, for each edge, whether it's part
    # of any such paths.

    distances = [z3.BitVec(f'distance-{i}', bits) for i in range(len(potential_nodes))]
    used_edge = [z3.Bool(f'used-edge-{i}') for i in range(len(edges))]

    # exactly one node is the source node
    is_zero_distance = [0 == d for d in distances]
    solver.add(z3.Or(*is_zero_distance))
    for (b1, b2) in itertools.combinations(is_zero_distance, 2):
        solver.add(z3.Not(z3.And(b1, b2)))

    def any_used_edges(edge_index_list):
        return z3.Or(*[used_edge[e] for e in edge_index_list])

    for i in range(len(potential_nodes)):
        is_node = potential_nodes[i]
        d = distances[i]
        is_source = is_zero_distance[i]

        incoming_edges = [x for x, e in enumerate(edges) if e[1] == i]
        outgoing_edges = [x for x, e in enumerate(edges) if e[0] == i]

        # the source node must be in the graph and have no used incoming_edges
        solver.add(
            z3.Implies(
                is_source,
                z3.And(is_node, z3.Not(any_used_edges(incoming_edges)))))

        # if this node and a neighbor are both in the graph, then this node must
        # be at most one further away than the neighbor (meaning it's connected)
        for e in incoming_edges:
            o = edges[e][0]
            solver.add(
                z3.Implies(z3.And(is_node, potential_nodes[o]),
                distances[i] <= distances[o]+1))

        # if this node is in the graph, then it must be connected by an edge.
        # conversely, if this node isn't in the graph, none of the edges can be used
        # (including the outgoing edges)
        solver.add(
            z3.Implies(
                z3.And(is_node, z3.Not(is_source)),
                any_used_edges(incoming_edges)))
        # not the converse is stronger (incluces outgoing_edges), so we can't simplify to an equivalence
        solver.add(z3.Implies(any_used_edges(incoming_edges+outgoing_edges), is_node))

        # if connected by an edge, then this node is exactly one distance away from the neighbor
        for e in incoming_edges:
            o = edges[e][0]
            solver.add(z3.Implies(used_edge[e], distances[i] == distances[o] + 1))
