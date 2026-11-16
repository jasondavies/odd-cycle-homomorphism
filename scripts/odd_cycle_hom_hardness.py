"""Multicoloured Clique -> homomorphism into an odd cycle.

The target is the cycle C_n for an odd n; the source has a feedback vertex set
of k+1 vertices. See ODD_CYCLE.md for the proof. Standard library only.
"""
import itertools

def reduce_clique(k, N, edges):
    """Classes 1..k, vertices (i,a) with a in 1..N. edges: set of ((i,a),(j,b)), i<j.
    Returns (number of source vertices, source edge list, n) with target C_n."""
    # Class i gets weight Q+i-1 with Q = 2Nk+1; vertex a of class i gets label a*weight.
    # These are the labels of the Lean proof; no two label differences between two
    # classes coincide, and none is the negative of another.
    p = [None] + [2 * N * k + 1 + i for i in range(k)]
    label = lambda i, a: a * p[i]
    M = N * (2 * N * k + 1 + k) + 2
    n = 2 * M + 1
    adj = []
    frame = lambda i, a: i * n + (a % n)
    count = (k + 1) * n
    for i in range(k + 1):
        for a in range(n):
            adj.append((frame(i, a), frame(i, a + 1)))
    def differ(x, y):
        nonlocal count
        prev = x
        for _ in range(n - 3):
            adj.append((prev, count)); prev = count; count += 1
        adj.append((prev, y))
    for i in range(1, k + 1):
        allowed = {label(i, a) % n for a in range(1, N + 1)}
        for d in range(n):
            if d not in allowed:
                differ(frame(0, d), frame(i, 0))
    for i in range(1, k + 1):
        for j in range(i + 1, k + 1):
            allowed = {(label(j, b) - label(i, a)) % n
                       for (u, v) in edges for (ii, a), (jj, b) in [(u, v)] if ii == i and jj == j}
            for d in range(n):
                if d not in allowed:
                    differ(frame(i, d), frame(j, 0))
    return count, adj, n

def hom_to_cycle(count, adj, n, fix=None, core=None):
    """Complete search knowing only the graph: arc consistency + backtracking on
    `core`, a set of vertices whose removal leaves a forest. Once the core is
    assigned, arc consistency is exact on the remaining forest; the completion is
    then built greedily and every edge is re-verified by the caller."""
    full = (1 << n) - 1
    nb = lambda D: ((D << 1) | (D >> (n - 1)) | (D >> 1) | (D << (n - 1))) & full
    nbrs = [[] for _ in range(count)]
    for u, v in adj:
        nbrs[u].append(v); nbrs[v].append(u)
    core = list(range(count)) if core is None else list(core)
    # the core really is a feedback vertex set
    inside = set(core); parent = list(range(count))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for u, v in adj:
        if u not in inside and v not in inside:
            ru, rv = find(u), find(v)
            assert ru != rv, "core is not a feedback vertex set"
            parent[ru] = rv
    dom = [full] * count
    for v, val in (fix or {}).items():
        dom[v] = 1 << val
    def propagate(dom, queue):
        queue = list(queue); inq = set(queue)
        while queue:
            v = queue.pop(); inq.discard(v)
            allowed = nb(dom[v])
            for w in nbrs[v]:
                new = dom[w] & allowed
                if new != dom[w]:
                    if not new:
                        return False
                    dom[w] = new
                    if w not in inq:
                        queue.append(w); inq.add(w)
        return True
    nodes = 0
    def search(dom):
        nonlocal nodes
        nodes += 1
        best, bc = -1, n + 1
        for v in core:
            d = dom[v]
            if d & (d - 1):
                c = bin(d).count("1")
                if c < bc:
                    best, bc = v, c
        if best < 0:
            for v in range(count):          # forest part: no backtracking needed
                d = dom[v]
                if d & (d - 1):
                    dom[v] = d & -d
                    assert propagate(dom, [v])
            return [d.bit_length() - 1 for d in dom]
        d = dom[best]
        while d:
            bit = d & -d; d ^= bit
            trial = list(dom); trial[best] = bit
            if propagate(trial, [best]):
                r = search(trial)
                if r is not None:
                    return r
        return None
    if not propagate(dom, range(count)):
        return None, nodes
    return search(dom), nodes

def has_clique(k, N, edges):
    es = set(edges)
    for choice in itertools.product(range(1, N + 1), repeat=k):
        if all(((i, choice[i - 1]), (j, choice[j - 1])) in es
               for i in range(1, k + 1) for j in range(i + 1, k + 1)):
            return True
    return False

def hubs(k, n):
    """The k+1 vertices whose removal leaves a forest: one per frame."""
    return [i * n for i in range(k + 1)]


def is_forest_without(count, adj, removed):
    removed = set(removed); parent = list(range(count))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for u, v in adj:
        if u in removed or v in removed:
            continue
        ru, rv = find(u), find(v)
        if ru == rv:
            return False
        parent[ru] = rv
    return True


def check(k, N, edges):
    """Compare the reduction with direct clique search on one instance."""
    count, adj, n = reduce_clique(k, N, edges)
    assert is_forest_without(count, adj, hubs(k, n))
    # By the symmetry of the target, the first frame may be placed by the identity.
    result, nodes = hom_to_cycle(count, adj, n, fix={0: 0, 1: 1}, core=range((k + 1) * n))
    if result is not None:
        assert all((result[u] - result[v]) % n in (1, n - 1) for u, v in adj)
    truth = has_clique(k, N, edges)
    assert (result is not None) == truth, (k, N, sorted(edges))
    return count, n, truth


# ---------------------------------------------------------------------------
# Chained Multicoloured Clique -> homomorphism into an odd cycle.
# r layers, k colours per layer, N vertices per layer-colour slot. Slot (t,c)
# has index s = t*k+c. Vertices are (t,c,a) with a in 1..N. A pair of slots is
# required when both lie in one layer or in consecutive layers.

def chained_cycle_length(K, N):
    return 2 * (N * (2 * N * K + 1 + K) + 2) + 1


def reduce_chained(r, k, N, edges):
    """Return (count, edge list, n, path decomposition bags, number of cycle vertices).

    Every slot has a reference cycle and a choice cycle. All reference cycles
    share their vertices 0 and 1 (source vertices 0 and 1), hence one edge.
    """
    K = r * k
    n = chained_cycle_length(K, N)
    weight = [2 * N * K + 1 + s for s in range(K)]
    label = lambda s, a: a * weight[s]
    layer = lambda s: s // k
    count = 2
    graph, ref, dial = set(), [], []

    def cycle(vs):
        for a, b in zip(vs, vs[1:] + vs[:1]):
            graph.add((min(a, b), max(a, b)))

    for s in range(K):
        ref.append([0, 1] + list(range(count, count + n - 2))); count += n - 2
        cycle(ref[s])
        dial.append(list(range(count, count + n))); count += n
        cycle(dial[s])
    base = count
    links = {}

    def link(start, end):
        nonlocal count
        path = [start] + list(range(count, count + n - 3)) + [end]
        count += n - 3
        for a, b in zip(path, path[1:]):
            graph.add((min(a, b), max(a, b)))
        return path

    for s in range(K):
        allowed = {label(s, a) % n for a in range(1, N + 1)}
        for d in range(n):
            if d not in allowed:
                links.setdefault(("ref", s, d), []).append(link(ref[s][d], dial[s][0]))
    slot = lambda v: v[0] * k + v[1]
    for s in range(K):
        for u in range(s + 1, K):
            if layer(u) > layer(s) + 1:
                continue
            allowed = {(label(u, y[2]) - label(s, x[2])) % n
                       for x, y in edges if slot(x) == s and slot(y) == u}
            for d in range(n):
                if d not in allowed:
                    links.setdefault(("dial", s, d), []).append(link(dial[s][d], dial[u][0]))

    # Explicit path decomposition: one phase per layer, keeping the two shared
    # reference vertices and the hubs of the current and the next layer.
    bags = []
    for t in range(r):
        keep = {0, 1} | {dial[s][0] for s in range(K) if layer(s) in (t, t + 1)}
        bags.append(set(keep))
        for s in range(t * k, (t + 1) * k):
            for kind, vs in (("ref", ref[s]), ("dial", dial[s])):
                for d, x in enumerate(vs):
                    bags.append(keep | {x})
                    for path in links.get((kind, s, d), []):
                        for a, b in zip(path, path[1:]):
                            bags.append(keep | {x, a, b})
                    bags.append(keep | {x, vs[(d + 1) % n]})
    return count, sorted(graph), n, bags, base


def check_path_decomposition(count, adj, bags, width):
    """Vertex coverage, edge coverage, interval occurrences and the width bound."""
    first, last, seen = [None] * count, [None] * count, [0] * count
    covered = set()
    for i, bag in enumerate(bags):
        assert len(bag) <= width + 1, (len(bag), width)
        for x in bag:
            if first[x] is None:
                first[x] = i
            last[x] = i
            seen[x] += 1
        covered.update(itertools.combinations(sorted(bag), 2))
    assert all(first[x] is not None and last[x] - first[x] + 1 == seen[x] for x in range(count))
    assert set(adj) <= covered
    return max(map(len, bags)) - 1


def has_chained_clique(r, k, N, edges):
    es = set(edges)
    for vals in itertools.product(range(1, N + 1), repeat=r * k):
        chosen = [(t, c, vals[t * k + c]) for t in range(r) for c in range(k)]
        if all((u, v) in es for u, v in itertools.combinations(chosen, 2) if v[0] - u[0] <= 1):
            return True
    return False


def check_chained(r, k, N, edges):
    """Compare the chained reduction with direct search on one instance."""
    count, adj, n, bags, base = reduce_chained(r, k, N, edges)
    width = check_path_decomposition(count, adj, bags, 2 * k + 4)
    # By the symmetry of the target, the shared reference edge is placed at (0,1).
    result, nodes = hom_to_cycle(count, adj, n, fix={0: 0, 1: 1}, core=range(base))
    if result is not None:
        assert all((result[u] - result[v]) % n in (1, n - 1) for u, v in adj)
    truth = has_chained_clique(r, k, N, edges)
    assert (result is not None) == truth, (r, k, N, sorted(edges))
    return count, n, width, truth
