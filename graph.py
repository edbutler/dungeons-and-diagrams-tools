import math
from typing import Any, Protocol
import z3
import itertools

class Solver(Protocol):
    def add(self, *args:Any) -> None: ...

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

