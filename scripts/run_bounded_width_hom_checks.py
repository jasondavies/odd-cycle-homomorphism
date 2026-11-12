"""Independent finite audits of the full entry-032 reduction. Standard library only."""
from itertools import product
import json
from pathlib import Path
import random

from bounded_width_hom_hardness import (
    ARROW_EDGES, ARROW_N, PORT_A, PORT_B, SCHEMA, COLOR_PRIME,
    lcs_instance, incidence, remove_colors, remove_directions,
    check_decomposition, graph_homomorphisms,
    reduce_lcs_to_graphs,
)

ROOT = Path(__file__).resolve().parents[1]


def csp(n, m, unary, binary):
    """Complete generic finite-domain oracle; knows nothing about strings or gadgets."""
    domains = [set(range(m)) for _ in range(n)]
    for v, allowed in unary:
        domains[v] &= allowed
    constraints = []
    for u, v, relation in binary:
        if u == v:
            domains[u] &= {a for a, b in relation if a == b}
        else:
            forward, backward = {}, {}
            for a, b in relation:
                forward.setdefault(a, set()).add(b)
                backward.setdefault(b, set()).add(a)
            constraints.extend([(u, v, forward), (v, u, backward)])

    def solve(ds):
        changed = True
        while changed:
            if any(not d for d in ds):
                return None
            changed = False
            for u, v, relation in constraints:
                keep = {a for a in ds[u] if relation.get(a, set()) & ds[v]}
                if keep != ds[u]:
                    ds[u] = keep
                    changed = True
        choice = min(((len(d), v) for v, d in enumerate(ds) if len(d) > 1), default=None)
        if choice is None:
            return tuple(next(iter(d)) for d in ds)
        _, v = choice
        for a in sorted(ds[v]):
            branch = [set(d) for d in ds]
            branch[v] = {a}
            result = solve(branch)
            if result is not None:
                return result
        return None

    return solve(domains)


def relational_hom(source, target):
    unary, binary = [], []
    for r, arity in SCHEMA.items():
        for fact in source.facts[r]:
            if arity == 1:
                unary.append((fact[0], {row[0] for row in target.facts[r]}))
            else:
                binary.append((*fact, target.facts[r]))
    result = csp(len(source.names), len(target.names), unary, binary)
    if result is not None:
        assert all(tuple(result[v] for v in fact) in target.facts[r]
                   for r in SCHEMA for fact in source.facts[r])
    return result


def subsequences(word):
    return {"".join(c for j, c in enumerate(word) if mask >> j & 1)
            for mask in range(1 << len(word))}


def incidence_labels(s):
    labels = [("domain", v) for v in range(len(s.names))]
    for r in SCHEMA:
        for fact in sorted(s.facts[r]):
            labels.append((r, fact))
            labels.extend((r, fact, i) for i in range(len(fact)))
    return labels


def check_map(arcs, target, mapping):
    assert all((mapping[u], mapping[v]) in target for u, v in arcs)


def full_pipeline(words, length, result):
    source, target, sd, td = lcs_instance(words, length)
    sc, sa, sd = incidence(source, sd)
    tc, ta, td = incidence(target, td)
    for colors, arcs, d in [(sc, sa, sd), (tc, ta, td)]:
        check_decomposition(len(colors), arcs, d)
    if result is not None:
        lookup = {label: i for i, label in enumerate(incidence_labels(target))}
        fm = []
        for label in incidence_labels(source):
            if label[0] == "domain":
                transformed = ("domain", result[label[1]])
            else:
                transformed = (label[0], tuple(result[v] for v in label[1]), *label[2:])
            fm.append(lookup[transformed])
        assert all(sc[v] == tc[fm[v]] for v in range(len(sc)))
        check_map(sa, ta, fm)

    sn, sa, sd = remove_colors(sc, sa, sd)
    tn, ta, td = remove_colors(tc, ta, td)
    sw = check_decomposition(sn, sa, sd)
    tw = check_decomposition(tn, ta, td)
    assert sw <= max(len(words) + 1, 2) and tw <= 3
    if result is not None:
        target_cycles, next_vertex = [], len(tc)
        for v, color in enumerate(tc):
            size = COLOR_PRIME[color]
            target_cycles.append([v] + list(range(next_vertex, next_vertex + size - 1)))
            next_vertex += size - 1
        roots = list(fm)
        for v, color in enumerate(sc):
            fm.extend(target_cycles[roots[v]][1:])
        assert len(fm) == sn
        check_map(sa, ta, fm)

    gn, ge, gd, gcopies = remove_directions(sn, sa, sd)
    hn, he, hd, hcopies = remove_directions(tn, ta, td)
    gw, hw = check_decomposition(gn, ge, gd), check_decomposition(hn, he, hd)
    assert gw <= max(len(words) + 1, 12) and hw <= 12
    if result is not None:
        gm = list(fm) + [-1] * (gn - sn)
        for (u, v), vertices in gcopies.items():
            image = hcopies[fm[u], fm[v]]
            for a, w in vertices.items():
                if a not in (PORT_A, PORT_B):
                    gm[w] = image[a]
        assert all(v >= 0 for v in gm)
        assert all(tuple(sorted((gm[u], gm[v]))) in he for u, v in ge)
    return {"words": words, "length": length, "answer": result is not None,
            "query_vertices": len(source.names), "target_vertices": len(target.names),
            "simple_source_vertices": gn, "simple_target_vertices": hn,
            "simple_source_width": gw, "simple_target_width": hw,
            "positive_map_checked": result is not None}


def main():
    for ws, length, expected in [([""], 0, True), ([""], 1, False),
                                  (["0", "1"], 5, False)]:
        g, h = reduce_lcs_to_graphs(ws, length)
        assert bool(list(graph_homomorphisms(g[0], g[1], h[0], h[1]))) == expected
        check_decomposition(*g)
        check_decomposition(*h)
    cases, yes = 0, 0
    max_qwidth = max_twidth = 0
    words = ["".join(bits) for n in range(1, 4) for bits in product("01", repeat=n)]
    instances = [(list(ws), length) for k in (1, 2, 3) for ws in product(words, repeat=k)
                 for length in range(1, min(map(len, ws)) + 1)]
    rng = random.Random(320026)
    instances += [(["".join(rng.choice("01") for _ in range(rng.randint(3, 6)))
                    for _ in range(k)], rng.randint(1, 3)) for k in (2, 3, 4) for _ in range(20)]
    for ws, length in instances:
        common = set.intersection(*(subsequences(w) for w in ws))
        truth = any(len(w) >= length for w in common)
        q, t, qd, td = lcs_instance(ws, length)
        qw = check_decomposition(len(q.names), q.edges(), qd)
        tw = check_decomposition(len(t.names), t.edges(), td)
        assert qw <= len(ws) + 1 and tw <= 3
        answer = relational_hom(q, t)
        assert (answer is not None) == truth, (ws, length)
        cases += 1
        yes += truth
        max_qwidth, max_twidth = max(max_qwidth, qw), max(max_twidth, tw)
        if cases % 1000 == 0:
            print("LCS equivalence checks", cases, flush=True)

    # Exhaust all homomorphisms of the explicit 13-vertex arrow into itself.
    endos = list(graph_homomorphisms(ARROW_N, ARROW_EDGES, ARROW_N, ARROW_EDGES))
    assert endos == [tuple(range(13))]
    adjacent = [set() for _ in range(13)]
    for u, v in ARROW_EDGES:
        adjacent[u].add(v)
        adjacent[v].add(u)
    cycles, lengths = set(), []

    def cycle(v, path):
        for w in adjacent[v]:
            if w == path[0] and len(path) >= 3:
                seq = tuple(path)
                cycles.add(min(seq, (seq[0],) + seq[:0:-1]))
            elif w > path[0] and w not in path:
                cycle(w, path + [w])

    def port_path(v, path):
        if v == PORT_B:
            lengths.append(len(path) - 1)
            return
        for w in adjacent[v] - set(path):
            port_path(w, path + [w])

    for v in range(13):
        cycle(v, [v])
    port_path(PORT_A, [PORT_A])
    assert sorted(map(len, cycles)) == [7, 7, 7, 8, 9, 10, 12]
    assert sorted(lengths) == [2, 7, 7, 7, 8, 10, 10]

    # All nonempty loopless 3-vertex digraphs: every H-map lands in one copy.
    possible = [(u, v) for u in range(3) for v in range(3) if u != v]
    arrow_cases = arrow_maps = 0
    for mask in range(1, 1 << len(possible)):
        arcs = {e for i, e in enumerate(possible) if mask >> i & 1}
        n, edges, d, copies = remove_directions(3, arcs, ([{0, 1, 2}], []))
        check_decomposition(n, edges, d)
        maps = set(graph_homomorphisms(13, ARROW_EDGES, n, edges))
        expected = {tuple(copy[v] for v in range(13)) for copy in copies.values()}
        assert maps == expected
        arrow_cases += 1
        arrow_maps += len(maps)
    print("Arrow gadget checks passed", flush=True)

    # Independently solve tiny colored DAGs and their prime-cycle encodings.
    prime_cases = 0
    tiny = []
    palette = [("domain",), ("Root",), ("Root", 0)]
    for colors in product(palette, repeat=2):
        if colors[0] == colors[1]:
            continue
        arcs = {(0, 1)}
        n, encoded, _ = remove_colors(colors, arcs, ([{0, 1}], []))
        tiny.append((colors, arcs, n, encoded))
    for sc, sa, sn, se in tiny:
        for tc, ta, tn, te in tiny:
            colored = csp(2, 2, [(v, {w for w in range(2) if sc[v] == tc[w]})
                                   for v in range(2)], [(u, v, ta) for u, v in sa])
            uncolored = csp(sn, tn, [], [(u, v, te) for u, v in se])
            assert (colored is not None) == (uncolored is not None)
            prime_cases += 1

    pipelines = []
    for ws, length in [(["0", "1"], 1), (["00", "0"], 1),
                       (["010", "101"], 2), (["010", "101"], 3),
                       (["010", "101", "110"], 2)]:
        q, t, _, _ = lcs_instance(ws, length)
        pipelines.append(full_pipeline(ws, length, relational_hom(q, t)))
        print("Full reduction checked", ws, length, flush=True)

    result = {"date": "2026-11-12", "scope": "Finite audits supplement the general written proof",
              "lcs_relational_comparisons": cases, "positive_cases": yes,
              "max_query_width": max_qwidth, "max_target_width": max_twidth,
              "arrow_endomorphisms": endos,
              "arrow_cycle_lengths": sorted(map(len, cycles)),
              "arrow_port_path_lengths": sorted(lengths),
              "arrow_target_digraphs": arrow_cases, "arrow_maps_checked": arrow_maps,
              "prime_encoding_comparisons": prime_cases,
              "full_pipeline_instances": pipelines}
    (ROOT / "sources/bounded-width-hom-results.json").write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: bounded-width homomorphism hardness audits", flush=True)


if __name__ == "__main__":
    main()
