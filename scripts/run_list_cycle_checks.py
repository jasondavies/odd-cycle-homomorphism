"""Exhaustive and seeded finite checks of the List Coloring reduction."""
from pathlib import Path
from collections import deque
import itertools
import json
import random

from verification import require

from list_cycle_hom import (
    Reduction, check_degeneracy, check_path_decomposition, check_tree_decomposition,
    hom_to_cycle, is_forest_without,
)


def powerset(values):
    values = list(values)
    for mask in range(1 << len(values)):
        yield {v for i, v in enumerate(values) if mask & (1 << i)}


def girth(count, edges):
    """Shortest cycle length by BFS from every vertex; None for a forest."""
    adj = [[] for _ in range(count)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    shortest = None
    for root in range(count):
        distance, parent = {root: 0}, {root: None}
        queue = deque([root])
        while queue:
            v = queue.popleft()
            for u in adj[v]:
                if u not in distance:
                    distance[u], parent[u] = distance[v] + 1, v
                    queue.append(u)
                elif parent[v] != u:
                    length = distance[v] + distance[u] + 1
                    shortest = length if shortest is None else min(shortest, length)
    return shortest


def verify(lists, edges, n, bags=None, tree=None, is_path=True, check_girth=False):
    m = len(lists)
    if bags is None:
        bags, tree = [set(range(m))], []
    width = max(0, max(map(len, bags))-1)
    check_tree_decomposition(m, edges, bags, tree, width)
    S = next(set(s) for k in range(m+1) for s in itertools.combinations(range(m), k)
             if is_forest_without(m, edges, s))
    g = Reduction(lists, edges, n)
    removed = S | {g.A, g.B}
    require(len(removed) == len(S) + 2)
    require(is_forest_without(g.count, g.edges, removed))
    td, tt = g.tree_decomposition(bags, tree)
    check_tree_decomposition(g.count, g.edges, td, tt, max(width+2, 4))
    if is_path:
        pd = g.path_decomposition(bags)
        check_path_decomposition(g.count, g.edges, pd, width+5)
    check_degeneracy(g.count, g.edges)
    hom, nodes = hom_to_cycle(g.count, g.edges, n, fix={g.A: 0, g.B: 1}, core=removed)
    expected = any(all(c[u] != c[v] for u, v in edges) for c in itertools.product(*lists))
    require((hom is not None) == expected, (lists, edges, n))
    if hom is not None:
        require(all((hom[u]-hom[v]) % n in (1, n-1) for u, v in g.edges))
    measured_girth = girth(g.count, g.edges) if check_girth else None
    if check_girth:
        require(measured_girth == (n if m else None), "Unexpected source girth")
    return {"satisfiable": expected, "source_vertices": g.count,
            "hom_search_nodes": nodes, "input_feedback_vertex_number": len(S),
            "target_length": n, "girth": measured_girth}


def main():
    cases = negative = max_vertices = total_search_nodes = positive_cyclic = girth_checks = 0
    targeted = []
    def run(*args, name=None, **kwargs):
        nonlocal cases, negative, max_vertices, total_search_nodes, positive_cyclic, girth_checks
        result = verify(*args, **kwargs)
        cases += 1
        negative += not result["satisfiable"]
        max_vertices = max(max_vertices, result["source_vertices"])
        total_search_nodes += result["hom_search_nodes"]
        positive_cyclic += result["satisfiable"] and result["input_feedback_vertex_number"] > 0
        girth_checks += kwargs.get("check_girth", False)
        if name:
            targeted.append({"name": name, **result})
    # Empty input, empty lists, isolated vertices, all binary-domain instances
    # on up to three vertices, and all three-color instances on two vertices.
    run([], set(), 5, name="empty input", check_girth=True)
    for m, q in [(1, 2), (2, 2), (3, 2), (2, 3)]:
        for lists in itertools.product(list(powerset(range(q))), repeat=m):
            for edges in powerset(itertools.combinations(range(m), 2)):
                run(lists, edges, 5)
    rng = random.Random(20261116)
    for case in range(160):
        q = (3, 5, 7)[case % 3]
        n = q+2
        m = 5
        lists = [{c for c in range(q) if rng.randrange(3)} for _ in range(m)]
        if case < 80:
            edges = {(i, i+1) for i in range(m-1) if rng.randrange(2)}
            bags = [{i, i+1} for i in range(m-1)]
            tree = [(i, i+1) for i in range(m-2)]
            run(lists, edges, n, bags, tree)
        else:
            edges = {(0, i) for i in range(1, m) if rng.randrange(2)}
            bags = [{0, i} for i in range(1, m)]
            tree = [(0, i) for i in range(1, m-1)]
            run(lists, edges, n, bags, tree, is_path=False)
    # Positive cyclic inputs exercise genuinely nonempty input feedback sets.
    run([{0, 1, 2}]*3, {(0, 1), (0, 2), (1, 2)}, 5,
        name="three-color triangle", check_girth=True)
    cyclic_edges = {(0, 1), (0, 2), (1, 2), (2, 3),
                    (3, 4), (3, 5), (4, 5), (3, 6)}
    cyclic_bags = [{0, 1, 2}, {2, 3}, {3, 4, 5}, {3, 6}]
    run([{0, 1, 2}]*7, cyclic_edges, 7, cyclic_bags, [(0, 1), (1, 2), (2, 3)],
        name="two triangles, bridge and leaf; staggered path", check_girth=True)
    run([{0, 1, 2}]*7, cyclic_edges, 7, cyclic_bags, [(0, 1), (1, 2), (1, 3)],
        name="two triangles, bridge and leaf; branching tree", is_path=False, check_girth=True)
    run([{0, 1, 2}]*4, set(itertools.combinations(range(4), 2)), 5,
        name="three-color K4", check_girth=True)
    report = {
        "cases": cases,
        "negative_instances": negative,
        "largest_source_vertices": max_vertices,
        "hom_search_nodes": total_search_nodes,
        "target_lengths": [5, 7, 9],
        "positive_cyclic_instances": positive_cyclic,
        "girth_checks": girth_checks,
        "targeted_cases": targeted,
        "checks": ["decision equivalence", "returned homomorphism edges",
                   "polynomial size bound", "tree decomposition",
                   "path decomposition (+5 direct sweep; Lean proves +6)",
                   "feedback vertex set transfer", "2-degeneracy",
                   "exact girth on targeted cases"],
        "passed": True,
        "scope": "Finite checks corroborate the construction; they do not prove universal statements.",
    }
    destination = Path(__file__).resolve().parents[1] / "reports/list-cycle-results.json"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
