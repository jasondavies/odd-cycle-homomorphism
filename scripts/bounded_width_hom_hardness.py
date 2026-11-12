"""Explicit LCS -> relational homomorphism -> digraph -> simple graph reduction.

Entry 032. Polynomial reduction, NOT an FPT homomorphism solver.
The accompanying proof supplies the hardness and all width bounds.
"""
from dataclasses import dataclass, field
from itertools import combinations


SCHEMA = {"Root": 1, "Next": 2, "Begin": 2, "Step": 2,
          "Advance": 2, "Letter": 2}
COLORS = [("domain",)] + [(r,) for r in SCHEMA] + [
    (r, i) for r, arity in SCHEMA.items() for i in range(arity)]
PRIMES = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67]
COLOR_PRIME = dict(zip(COLORS, PRIMES))


@dataclass
class Structure:
    names: list = field(default_factory=list)
    facts: dict = field(default_factory=lambda: {r: set() for r in SCHEMA})

    def vertex(self, name):
        v = len(self.names)
        self.names.append(name)
        return v

    def add(self, relation, *values):
        assert len(values) == SCHEMA[relation]
        self.facts[relation].add(tuple(values))

    def edges(self):
        return {tuple(sorted((u, v))) for facts in self.facts.values() for fact in facts
                for u, v in combinations(fact, 2) if u != v}


def lcs_instance(words, length):
    """Nontrivial inputs only; trivial yes/no instances are preprocessed separately.

    Return query, target, and certified-width decompositions (bags, tree edges).
    """
    assert words and 1 <= length <= min(map(len, words))
    k, bound = len(words), max(map(len, words))
    query, target = Structure(), Structure()
    anchors = [target.vertex(("anchor", i)) for i in range(k + 1)]
    letters = {a: target.vertex(("letter", a)) for a in sorted(set("".join(words)))}
    target.add("Root", anchors[0])
    positions = []
    for i, word in enumerate(words, 1):
        target.add("Next", anchors[i - 1], anchors[i])
        row = [target.vertex((i, j)) for j in range(len(word) + 1)]
        positions.append(row)
        target.add("Begin", anchors[i], row[0])
        for j, v in enumerate(row):
            target.add("Step", v, v)
            if j:
                target.add("Step", row[j - 1], v)
                target.add("Advance", row[j - 1], v)
                target.add("Letter", v, letters[word[j - 1]])

    # Removing the letter vertices leaves a tree. Add them to its edge bags.
    apex = set(letters.values())
    forest_edges = target.edges() - {edge for edge in target.edges() if set(edge) & apex}
    adjacent = {v: [] for v in range(len(target.names)) if v not in apex}
    for u, v in forest_edges:
        adjacent[u].append(v)
        adjacent[v].append(u)
    tbags, ttree = [apex | {anchors[0]}], []
    todo = [(anchors[0], -1, 0)]
    while todo:
        v, parent, bag = todo.pop()
        for w in adjacent[v]:
            if w != parent:
                new = len(tbags)
                tbags.append(apex | {v, w})
                ttree.append((bag, new))
                todo.append((w, v, new))

    qanchors = [query.vertex(("anchor", i)) for i in range(k + 1)]
    query.add("Root", qanchors[0])
    qbags, frontier = [{qanchors[0]}], []
    for i in range(k):
        qbags.append(set(frontier) | {qanchors[i], qanchors[i + 1]})
        query.add("Next", qanchors[i], qanchors[i + 1])
        x = query.vertex((i, 0))
        frontier.append(x)
        query.add("Begin", qanchors[i + 1], x)
        qbags.append(set(frontier) | {qanchors[i + 1]})
    qbags.append(set(frontier))
    for j in range(1, length + 1):
        z = query.vertex(("common letter", j))
        qbags.append(set(frontier) | {z})
        for i in range(k):
            for step in range(bound + 1):
                x = query.vertex((i, j, step))
                qbags.append(set(frontier) | {z, x})
                query.add("Step" if step < bound else "Advance", frontier[i], x)
                frontier[i] = x
            query.add("Letter", x, z)
        qbags.append(set(frontier))
    return query, target, (qbags, list(zip(range(len(qbags) - 1), range(1, len(qbags))))), (tbags, ttree)


def check_decomposition(n, edges, decomposition):
    """Independent direct check of coverage, running intersection, and tree shape."""
    bags, tree = decomposition
    bags = list(map(set, bags))
    assert bags and len(tree) == len(bags) - 1
    adjacent = [set() for _ in bags]
    for u, v in tree:
        assert u != v and v not in adjacent[u]
        adjacent[u].add(v)
        adjacent[v].add(u)

    def connected(allowed):
        reached, stack = set(), [next(iter(allowed))]
        while stack:
            v = stack.pop()
            if v not in reached:
                reached.add(v)
                stack.extend(adjacent[v] & allowed - reached)
        return reached == allowed

    assert connected(set(range(len(bags))))
    assert set().union(*bags) == set(range(n))
    occurrences = [set() for _ in range(n)]
    for i, bag in enumerate(bags):
        for v in bag:
            occurrences[v].add(i)
    for u, v in edges:
        assert occurrences[u] & occurrences[v]
    assert all(connected(where) for where in occurrences)
    return max(map(len, bags)) - 1


def incidence(structure, decomposition):
    """Typed acyclic incidence digraph, with every vertex incident to a typed arc."""
    colors = [("domain",)] * len(structure.names)
    arcs = set()
    bags, tree = [set(b) for b in decomposition[0]], list(decomposition[1])
    for relation in SCHEMA:
        for fact in sorted(structure.facts[relation]):
            parent = next(i for i, bag in enumerate(bags) if set(fact) <= bag)
            t = len(colors)
            colors.append((relation,))
            central = len(bags)
            bags.append(set(fact) | {t})
            tree.append((parent, central))
            for i, value in enumerate(fact):
                p = len(colors)
                colors.append((relation, i))
                arcs.update([(t, p), (p, value)])
                tree.append((central, len(bags)))
                bags.append({t, p, value})
    assert set().union(*map(set, arcs)) == set(range(len(colors)))
    return colors, arcs, (bags, tree)


def remove_colors(colors, arcs, decomposition):
    """Attach distinct-prime directed cycles to the roots of the typed DAG."""
    out = set(arcs)
    n = len(colors)
    bags, tree = [set(b) for b in decomposition[0]], list(decomposition[1])
    for v, color in enumerate(colors):
        p = COLOR_PRIME[color]
        cycle = [v] + list(range(n, n + p - 1))
        n += p - 1
        out.update(zip(cycle, cycle[1:] + cycle[:1]))
        parent = next(i for i, bag in enumerate(bags) if v in bag)
        for j in range(1, p - 1):
            tree.append((parent, len(bags)))
            parent = len(bags)
            bags.append({v, cycle[j], cycle[j + 1]})
    return n, out, (bags, tree)


# A,B,C,D are the branch vertices 0,1,2,3. Port a=4; port b=6.
# This is G_1 in Eleftheriadis (2024), Definition 2.6.
ARROW_PATHS = [(0, 1), (0, 4, 5, 2), (0, 6, 7, 8, 3),
               (1, 9, 10, 2), (1, 11, 3), (2, 12, 3)]
ARROW_EDGES = {tuple(sorted(e)) for path in ARROW_PATHS for e in zip(path, path[1:])}
ARROW_N, PORT_A, PORT_B = 13, 4, 6


def remove_directions(n, arcs, decomposition):
    assert all(u != v for u, v in arcs)
    bags, tree = [set(b) for b in decomposition[0]], list(decomposition[1])
    containing = {tuple(sorted((u, v))): i for i, bag in enumerate(bags)
                  for u, v in combinations(bag, 2)}
    out, copies = set(), {}
    for u, v in sorted(arcs):
        vertices = {PORT_A: u, PORT_B: v}
        for x in range(ARROW_N):
            if x not in vertices:
                vertices[x] = n
                n += 1
        parent = containing[tuple(sorted((u, v)))]
        tree.append((parent, len(bags)))
        bags.append(set(vertices.values()))
        out.update(tuple(sorted((vertices[a], vertices[b]))) for a, b in ARROW_EDGES)
        copies[u, v] = vertices
    return n, out, (bags, tree), copies


def reduce_lcs_to_graphs(words, length):
    """Return (G,H), each as (number of vertices, edge set, decomposition).

    Accepts every nonempty list of binary strings and nonnegative target length.
    G -> H iff the strings have a common subsequence of at least that length.
    """
    assert words and isinstance(length, int) and length >= 0
    assert all(set(word) <= {"0", "1"} for word in words)
    singleton = (1, set(), ([{0}], []))
    if length == 0:
        return singleton, singleton
    if length > min(map(len, words)):
        return (2, {(0, 1)}, ([{0, 1}], [])), singleton
    source, target, sd, td = lcs_instance(words, length)
    graphs = []
    for structure, decomposition in [(source, sd), (target, td)]:
        colors, arcs, decomposition = incidence(structure, decomposition)
        n, arcs, decomposition = remove_colors(colors, arcs, decomposition)
        n, edges, decomposition, _ = remove_directions(n, arcs, decomposition)
        graphs.append((n, edges, decomposition))
    return tuple(graphs)


def graph_homomorphisms(n, edges, m, target_edges, limit=None):
    """Complete finite oracle using only adjacency, for gadget audits."""
    adjacent = [set() for _ in range(n)]
    target = [set() for _ in range(m)]
    for u, v in edges:
        adjacent[u].add(v)
        adjacent[v].add(u)
    for u, v in target_edges:
        target[u].add(v)
        target[v].add(u)
    assignment, found = {}, 0

    def visit():
        nonlocal found
        if len(assignment) == n:
            found += 1
            yield tuple(assignment[v] for v in range(n))
            return
        choices = []
        for v in range(n):
            if v in assignment:
                continue
            domain = set(range(m))
            for u in adjacent[v] & assignment.keys():
                domain &= target[assignment[u]]
            choices.append((len(domain), -len(adjacent[v] & assignment.keys()), v, domain))
        _, _, v, domain = min(choices, key=lambda item: item[:3])
        for value in sorted(domain):
            assignment[v] = value
            yield from visit()
            del assignment[v]
            if limit is not None and found >= limit:
                return

    yield from visit()
