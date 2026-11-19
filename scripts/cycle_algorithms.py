"""Reference algorithms for circular-clique thresholds and long odd cycles."""
import argparse
import json
import sys
from collections import deque
from fractions import Fraction
from itertools import product


def _graph(order, edges):
    if type(order) is not int or order < 0:
        raise ValueError("order must be a nonnegative integer")
    adj = [set() for _ in range(order)]
    for u, v in edges:
        if (type(u) is not int or type(v) is not int or
                not (0 <= u < order and 0 <= v < order) or u == v):
            raise ValueError("edges must join distinct vertices in range(order)")
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _distances(size, arcs, root):
    """Bellman–Ford from one root. Every vertex in these systems is reachable."""
    dist = {root: 0}
    for _ in range(size):
        changed = False
        for u, v, weight in arcs:
            if u not in dist:
                continue
            bound = dist[u] + weight
            if v not in dist or bound < dist[v]:
                dist[v] = bound
                changed = True
        if not changed:
            return dist
    return None  # reachable negative cycle


def _chains(adj):
    """Consume the adjacency sets. Encode each pure cycle as a closed chain."""
    leaves = deque(v for v, neighbors in enumerate(adj) if len(neighbors) == 1)
    while leaves:
        u = leaves.popleft()
        if adj[u]:
            v = adj[u].pop()
            adj[v].remove(u)
            if len(adj[v]) == 1:
                leaves.append(v)

    branches = [v for v, neighbors in enumerate(adj) if len(neighbors) > 2]
    degree_two = {v for v, neighbors in enumerate(adj) if len(neighbors) == 2}
    chains = []
    # Trace from branch vertices first. Only pure cycles have edges left after that.
    for start in (*branches, *degree_two):
        while adj[start]:
            u = start
            length = 0
            while True:
                v = adj[u].pop()
                adj[v].remove(u)
                length += 1
                if v == start or v not in degree_two:
                    break
                u = v
            chains.append((start, v, length))
    return chains


def _threshold(chains, p, q):
    fixed = []
    endpoints = set()
    choices = []
    for u, v, length in chains:
        low = length * q
        high = length * (p - q)
        if u == v:
            if (low + p - 1) // p > high // p:
                return False
            continue
        width = high - low
        if width >= p - 1:
            continue
        endpoints.update((u, v))
        start = low % p
        intervals = []
        for offset in (-2 * p, -p, 0):
            a = max(1 - p, start + offset)
            b = min(p - 1, start + offset + width)
            if a <= b:
                intervals.append(((u, v, b), (v, u, -a)))
        choices.append(intervals)

    # Coordinate bounds relative to a common zero, outside the vertex index range.
    zero = -1
    for v in endpoints:
        fixed.extend(((zero, v, p - 1), (v, zero, 0)))
    for selection in product(*choices):
        arcs = fixed + [arc for pair in selection for arc in pair]
        if _distances(len(endpoints) + 1, arcs, zero) is not None:
            return True
    return False


def circular_clique(order, edges, p, q):
    """Decide G → K_(p/q) in 2^O(r) times a polynomial in the input bits."""
    if type(p) is not int or type(q) is not int or q < 1 or p < 2 * q:
        raise ValueError("expected integer p >= 2q >= 2")
    return _threshold(_chains(_graph(order, edges)), p, q)


def circular_chromatic_number(order, edges):
    """Compute the exact circular chromatic number as a Fraction."""
    adj = _graph(order, edges)
    if not any(adj):
        return Fraction(int(order > 0))
    chains = _chains(adj)
    if _threshold(chains, 2, 1):
        return Fraction(2)
    # Finite attainment bounds the numerator. Feasibility is monotone in p/q.
    candidates = sorted({Fraction(p, q) for p in range(3, order + 1)
                         for q in range(1, p // 2 + 1)})
    lo, hi = 0, len(candidates) - 1
    while lo < hi:
        mid = (lo + hi) // 2
        ratio = candidates[mid]
        if _threshold(chains, ratio.numerator, ratio.denominator):
            hi = mid
        else:
            lo = mid + 1
    return candidates[lo]


def _tree_tour(adj, root):
    """Record parents, depths and first visits on a depth-first tree tour."""
    parent = {root: None}
    depth = {root: 0}
    first = {root: 0}
    stack = [(root, iter(adj[root]))]
    time = 0
    while stack:
        u, children = stack[-1]
        v = next(children, None)
        if v is None:
            stack.pop()
            time += 1  # return along the parent edge
        elif v not in parent:
            time += 1
            first[v] = time
            parent[v] = u
            depth[v] = depth[u] + 1
            stack.append((v, iter(adj[v])))
    return parent, depth, first


def _sampled_colouring(root, depth, first, tree_arcs, chords, ell):
    step = (ell - 1) // 3
    last = max(first[v] // step for edge in chords for v in edge)
    batches = [[] for _ in range(last + 1)]
    for u, v in chords:
        i, j = first[u] // step, first[v] // step
        batches[max(i, j)].append((u, v, i, j))

    # Depth-first enumeration. Store only pending siblings along the current branch.
    stack = [([0], tree_arcs)]
    while stack:
        blocks, previous = stack.pop()
        index = len(blocks) - 1
        arcs = previous.copy()
        for u, v, i, j in batches[index]:
            centre = (blocks[j] - blocks[i]) * step
            low, high = centre - 3 * step, centre + 3 * step
            k = -((-low) // ell)  # ceiling division, also for negative bounds
            k += (depth[v] - depth[u] - 1 - k) % 2
            if k * ell > high:
                break
            arcs.extend(((u, v, k * ell + 1), (v, u, 1 - k * ell)))
        else:
            if index < last:
                for delta in (-1, 1, 0):
                    stack.append((blocks + [blocks[-1] + delta], arcs))
            else:
                # Distances from this tree root have the required depth parity.
                dist = _distances(len(depth), arcs, root)
                if dist is not None:
                    return {v: h % ell for v, h in dist.items()}
    return None


def long_cycle_homomorphism(order, edges, ell):
    """Return a list of colours witnessing G → C_ell, or None, in 2^O(N/ell) poly time."""
    if type(ell) is not int or ell < 3 or ell % 2 == 0:
        raise ValueError("expected an odd cycle length >= 3")
    adj = _graph(order, edges)
    colours = [None] * order
    for root in range(order):
        if colours[root] is not None:
            continue
        parent, depth, first = _tree_tour(adj, root)
        chords = [(u, v) for u in parent for v in adj[u]
                  if u < v and parent[u] != v and parent[v] != u]
        if all((depth[u] - depth[v]) % 2 for u, v in chords):
            component = {v: d % 2 for v, d in depth.items()}
        elif ell > len(parent):
            return None
        elif ell == 3:
            children = [v for v in parent if v != root]
            for signs in product((-1, 1), repeat=len(children)):
                component = {root: 0}
                for v, sign in zip(children, signs):
                    component[v] = (component[parent[v]] + sign) % ell
                if all(component[u] != component[v] for u, v in chords):
                    break
            else:
                return None
        else:
            tree_arcs = []
            for v, u in parent.items():
                if v != root:
                    tree_arcs.extend(((u, v, 1), (v, u, 1)))
            component = _sampled_colouring(root, depth, first, tree_arcs, chords, ell)
            if component is None:
                return None
        for v, colour in component.items():
            colours[v] = colour
    return colours


def main():
    parser = argparse.ArgumentParser(description="Read a graph with order and edges as JSON on stdin.")
    commands = parser.add_subparsers(dest="algorithm", required=True)
    commands.add_parser("long-cycle").add_argument("ell", type=int)
    threshold = commands.add_parser("circular-clique")
    threshold.add_argument("p", type=int)
    threshold.add_argument("q", type=int)
    commands.add_parser("circular-number")
    args = parser.parse_args()
    try:
        graph = json.load(sys.stdin)
        order, edges = graph["order"], graph["edges"]
        if args.algorithm == "long-cycle":
            result = long_cycle_homomorphism(order, edges, args.ell)
        elif args.algorithm == "circular-clique":
            result = circular_clique(order, edges, args.p, args.q)
        else:
            result = str(circular_chromatic_number(order, edges))
    except (KeyError, TypeError, ValueError) as exc:
        parser.error(str(exc))
    print(json.dumps(result))


if __name__ == "__main__":
    main()
