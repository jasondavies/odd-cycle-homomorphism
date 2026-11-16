"""Exhaustive and seeded finite checks of the List Coloring reduction."""
from pathlib import Path
import itertools
import json
import random

from list_cycle_hom import (
    Reduction, check_degeneracy, check_path_decomposition, check_tree_decomposition,
    hom_to_cycle, is_forest_without,
)


def powerset(values):
    values = list(values)
    for mask in range(1 << len(values)):
        yield {v for i, v in enumerate(values) if mask & (1 << i)}


def verify(lists, edges, n, bags=None, tree=None, is_path=True):
    m = len(lists)
    if bags is None:
        bags, tree = [set(range(m))], []
    width = max(0, max(map(len, bags))-1)
    check_tree_decomposition(m, edges, bags, tree, width)
    S = next(set(s) for k in range(m+1) for s in itertools.combinations(range(m), k)
             if is_forest_without(m, edges, s))
    g = Reduction(lists, edges, n)
    removed = S | {g.A, g.B}
    assert len(removed) == len(S) + 2
    assert is_forest_without(g.count, g.edges, removed)
    td, tt = g.tree_decomposition(bags, tree)
    check_tree_decomposition(g.count, g.edges, td, tt, max(width+2, 4))
    if is_path:
        pd = g.path_decomposition(bags)
        check_path_decomposition(g.count, g.edges, pd, width+5)
    check_degeneracy(g.count, g.edges)
    hom, nodes = hom_to_cycle(g.count, g.edges, n, fix={g.A: 0, g.B: 1}, core=removed)
    expected = any(all(c[u] != c[v] for u, v in edges) for c in itertools.product(*lists))
    assert (hom is not None) == expected, (lists, edges, n)
    if hom is not None:
        assert all((hom[u]-hom[v]) % n in (1, n-1) for u, v in g.edges)
    return expected, g.count, nodes


def main():
    cases = negative = max_vertices = total_search_nodes = 0
    def run(*args, **kwargs):
        nonlocal cases, negative, max_vertices, total_search_nodes
        sat, vertices, nodes = verify(*args, **kwargs)
        cases += 1
        negative += not sat
        max_vertices = max(max_vertices, vertices)
        total_search_nodes += nodes
    # Empty input, empty lists, isolated vertices, all binary-domain instances
    # on up to three vertices, and all three-color instances on two vertices.
    run([], set(), 5)
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
    report = {
        "cases": cases,
        "negative_instances": negative,
        "largest_source_vertices": max_vertices,
        "hom_search_nodes": total_search_nodes,
        "target_lengths": [5, 7, 9],
        "checks": ["decision equivalence", "returned homomorphism edges",
                   "polynomial size bound", "tree decomposition",
                   "path decomposition (+5 direct sweep; Lean proves +6)",
                   "feedback vertex set transfer", "2-degeneracy"],
        "passed": True,
        "scope": "Finite checks corroborate the construction; they do not prove universal statements.",
    }
    destination = Path(__file__).resolve().parents[1] / "sources/list-cycle-results.json"
    destination.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
