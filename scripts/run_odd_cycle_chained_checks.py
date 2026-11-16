"""Finite audits of the chained odd-cycle reduction; they supplement ODD_CYCLE.md."""
from itertools import combinations
import json
from pathlib import Path
import random

from odd_cycle_hom_hardness import check_chained

ROOT = Path(__file__).resolve().parents[1]


def candidates(r, k, N):
    vs = [(t, c, a) for t in range(r) for c in range(k) for a in range(1, N + 1)]
    return [(u, v) for u, v in combinations(vs, 2) if u[:2] != v[:2] and v[0] - u[0] <= 1]


def main():
    report = []

    def run(label, r, k, N, instances):
        total = yes = size = width = 0
        for edges in instances:
            count, n, w, truth = check_chained(r, k, N, edges)
            total += 1
            yes += truth
            size, width = max(size, count), max(width, w)
        report.append({"family": label, "layers": r, "colours": k, "class_size": N,
                       "instances": total, "with_clique": yes, "without_clique": total - yes,
                       "target_cycle_length": n, "max_source_vertices": size,
                       "max_path_decomposition_width": width, "width_bound": 2 * k + 4})
        print("PASS", label, (r, k, N), total, "instances;", yes, "yes,", total - yes, "no;",
              "width", width, flush=True)

    for r, k, N in [(2, 1, 2), (3, 1, 2), (2, 2, 1)]:
        ps = candidates(r, k, N)
        run("all instances", r, k, N, ({p for j, p in enumerate(ps) if mask >> j & 1}
                                       for mask in range(1 << len(ps))))
    # Each adjacent pair of layers is feasible alone, but not with a common middle choice.
    run("inconsistent middle layer", 3, 1, 2, [{((0, 0, 1), (1, 0, 1)), ((1, 0, 2), (2, 0, 1))}])
    rng = random.Random(8621)
    for r, k, N, number in [(3, 2, 2, 10), (4, 2, 2, 6), (3, 3, 2, 2)]:
        ps = candidates(r, k, N)
        cases = [set(), set(ps)]
        for _ in range(number):
            density = rng.choice([.6, .8, .95])
            cases.append({p for p in ps if rng.random() < density})
        run("seeded", r, k, N, cases)
    result = {"date": "2026-11-16",
              "scope": "Finite audits supplement the written proof; they are not a proof",
              "families": report,
              "total_instances": sum(row["instances"] for row in report)}
    (ROOT / "sources/odd-cycle-chained-results.json").write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: chained odd-cycle homomorphism hardness audits", flush=True)


if __name__ == "__main__":
    main()
