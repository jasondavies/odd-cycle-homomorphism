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
