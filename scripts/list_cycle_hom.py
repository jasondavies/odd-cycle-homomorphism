"""List Coloring to odd-cycle homomorphism; finite validation utilities."""
import itertools

from verification import require


class Reduction:
    """Construct precisely the reference copies and links used by Lean.

    Reference copies exist for all (vertex, residue) pairs, including allowed
    colors. Only forbidden pairs receive a domain link. Vertex numbering differs
    from the Lean sum type, but all adjacencies agree with that definition.
    """
    def __init__(self, lists, edges, n):
        require(n >= 5 and n % 2 == 1)
        self.m, self.n = len(lists), n
        require(all(set(domain) <= set(range(n)) for domain in lists))
        self.count = self.m + 2
        self.A, self.B = self.m, self.m + 1
        self.edges = {(self.A, self.B)}
        self.parts, self.sweeps = [], []
        for v, domain in enumerate(lists):
            for d in range(n):
                start = self.count
                cycle = [self.A, self.B] + [self.vertex() for _ in range(n - 2)]
                for i in range(n):
                    self.edge(cycle[i], cycle[(i + 1) % n])
                link = self.link(cycle[d], v) if d not in domain else None
                self.parts.append(({self.A, self.B, v}, list(range(start, self.count))))
                self.sweeps.append(({v}, cycle, link, d))
        for u, v in sorted(edges):
            require(0 <= u < v < self.m)
            start = self.count
            link = self.link(u, v)
            self.parts.append(({u, v}, list(range(start, self.count))))
            self.sweeps.append(({u, v}, None, link, None))
        forbidden = sum(n - len(domain) for domain in lists)
        require(self.count == 2 + self.m + self.m*n*(n-2) + (forbidden+len(edges))*(n-3))
        require(self.count <= 2+self.m+self.m*n*n+(self.m*n+self.m*self.m)*n)

    def vertex(self):
        v = self.count
        self.count += 1
        return v

    def edge(self, u, v):
        require(u != v)
        self.edges.add(tuple(sorted((u, v))))

    def link(self, u, v):
        path = [u] + [self.vertex() for _ in range(self.n - 3)] + [v]
        for a, b in zip(path, path[1:]):
            self.edge(a, b)
        return path

    def tree_decomposition(self, original_bags, original_tree):
        """Root each reference tree at its hub attachment, then add the anchors.

        Reference bags have size at most four. Original-edge subdivisions
        use bags of size three, giving width max(w+2, 3).
        """
        bags = [set(b) | {self.A, self.B} for b in original_bags]
        tree = list(original_tree)
        adj = [[] for _ in range(self.count)]
        for u, v in self.edges:
            adj[u].append(v)
            adj[v].append(u)
        anchors = {self.A, self.B}
        for boundary, internal in self.parts:
            owner = next(i for i, b in enumerate(original_bags)
                         if boundary - anchors <= set(b))
            if not anchors <= boundary:
                u, v = sorted(boundary)
                parent_bag, previous = owner, u
                for x in internal:
                    bi = len(bags)
                    bags.append({v, previous, x})
                    tree.append((parent_bag, bi))
                    parent_bag, previous = bi, x
                continue
            hub, = boundary - anchors
            unseen = set(internal)
            while unseen:
                attached = [x for x in unseen if hub in adj[x]]
                root = min(attached) if attached else min(unseen)
                unseen.remove(root)
                queue = [(root, hub if attached else None, owner)]
                while queue:
                    v, parent, parent_bag = queue.pop()
                    bi = len(bags)
                    bags.append(anchors | {v} | ({parent} if parent is not None else set()))
                    tree.append((parent_bag, bi))
                    for u in adj[v]:
                        if u in anchors or u == parent:
                            continue
                        require(u in unseen, "reference attachment is not a forest")
                        unseen.remove(u)
                        queue.append((u, v, bi))
        return bags, tree

    def path_decomposition(self, original_bags):
        """Direct sweep with an additive pathwidth bound of +5.

        Lean uses a modular argument with the conservative +6 bound.
        """
        bags = []
        for bi, b in enumerate(original_bags):
            base = set(b) | {self.A, self.B}
            bags.append(base)
            for boundary, cycle, link, d in self.sweeps:
                owner = next(j for j, c in enumerate(original_bags) if boundary <= set(c))
                if owner != bi:
                    continue
                def sweep(keep):
                    if link is not None:
                        for x, y in zip(link, link[1:]):
                            bags.append(base | keep | {x, y})
                if cycle is None:
                    sweep(set())
                else:
                    if d in (0, 1):
                        sweep(set())
                    for i in range(2, self.n):
                        bags.append(base | {cycle[i-1], cycle[i]})
                        if d == i:
                            sweep({cycle[i]})
                    bags.append(base | {cycle[-1]})
            bags.append(base)
        return bags


def check_tree_decomposition(count, edges, bags, tree, width):
    require(bool(bags), "A tree decomposition must have at least one bag")
    require(all(isinstance(i, int) and 0 <= i < len(bags)
                for edge in tree for i in edge), "Invalid decomposition-tree endpoint")
    require(is_forest_without(len(bags), tree, ()))
    require(len(tree) == len(bags) - 1)
    occurrences, common = [0]*count, [0]*count
    covered = set()
    for bag in bags:
        require(len(bag) <= width + 1)
        require(all(isinstance(v, int) and 0 <= v < count for v in bag),
                "Invalid bag vertex")
        for v in bag:
            occurrences[v] += 1
        covered.update(itertools.combinations(sorted(bag), 2))
    require(set(edges) <= covered)
    for i, j in tree:
        for v in bags[i] & bags[j]:
            common[v] += 1
    # A nonempty induced subgraph of a tree is connected iff it has |V|-1 edges.
    require(all(occurrences[v] > 0 and common[v] == occurrences[v]-1 for v in range(count)))
    return max(map(len, bags)) - 1


def check_degeneracy(count, edges, k=2):
    adj = [set() for _ in range(count)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    queue = [v for v in range(count) if len(adj[v]) <= k]
    removed = set()
    while queue:
        v = queue.pop()
        if v in removed:
            continue
        removed.add(v)
        for u in adj[v]:
            adj[u].remove(v)
            if len(adj[u]) <= k:
                queue.append(u)
    require(len(removed) == count)

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
            require(ru != rv, "core is not a feedback vertex set")
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
                    if not propagate(dom, [v]):
                        raise RuntimeError("Arc consistency failed during forest completion")
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

def check_path_decomposition(count, adj, bags, width):
    """Vertex coverage, edge coverage, interval occurrences and the width bound."""
    require(bool(bags), "A path decomposition must have at least one bag")
    first, last, seen = [None] * count, [None] * count, [0] * count
    covered = set()
    for i, bag in enumerate(bags):
        require(len(bag) <= width + 1, (len(bag), width))
        require(all(isinstance(x, int) and 0 <= x < count for x in bag),
                "Invalid bag vertex")
        for x in bag:
            if first[x] is None:
                first[x] = i
            last[x] = i
            seen[x] += 1
        covered.update(itertools.combinations(sorted(bag), 2))
    require(all(first[x] is not None and last[x] - first[x] + 1 == seen[x] for x in range(count)))
    require(set(adj) <= covered)
    return max(map(len, bags)) - 1
