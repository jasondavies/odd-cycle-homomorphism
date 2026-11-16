"""Finite audits of the odd-cycle reduction; they supplement the proof in ODD_CYCLE.md."""
from itertools import product
import json
from pathlib import Path
import random

from odd_cycle_hom_hardness import check

ROOT = Path(__file__).resolve().parents[1]


def pairs(k, N):
    return [((i, a), (j, b)) for i in range(1, k + 1) for j in range(i + 1, k + 1)
            for a in range(1, N + 1) for b in range(1, N + 1)]


def main():
    # The walk-length fact behind the "different images" paths.
    for n in range(5, 40, 2):
        full = (1 << n) - 1
        reach = 1
        for _ in range(n - 2):
            reach = ((reach << 1) | (reach >> (n - 1)) | (reach >> 1) | (reach << (n - 1))) & full
        assert reach == full ^ 1
    rng = random.Random(11)
    report = []

    def run(label, k, N, instances):
        total = yes = 0
        for edges in instances:
            count, n, truth = check(k, N, edges)
            total += 1
            yes += truth
        report.append({"family": label, "classes": k, "class_size": N, "instances": total,
                       "with_clique": yes, "without_clique": total - yes,
                       "target_cycle_length": n, "last_source_vertices": count})
        print("PASS", label, total, "instances;", yes, "yes,", total - yes, "no", flush=True)

    p = pairs(2, 2)
    run("all instances", 2, 2, [{p[t] for t in range(len(p)) if mask >> t & 1}
                                 for mask in range(1 << len(p))])
    p = pairs(3, 2)
    run("all instances", 3, 2, [{p[t] for t in range(len(p)) if mask >> t & 1}
                                 for mask in range(1 << len(p))])
    p = pairs(4, 2)
    run("random", 4, 2, [{x for x in p if rng.random() < rng.choice([0.55, 0.65, 0.75])}
                         for _ in range(150)])
    p = pairs(3, 3)
    run("random", 3, 3, [{x for x in p if rng.random() < rng.choice([0.3, 0.4, 0.5])}
                         for _ in range(120)])
    result = {"date": "2026-11-16",
              "scope": "Finite audits supplement the written proof; they are not a proof",
              "families": report,
              "total_instances": sum(r["instances"] for r in report)}
    (ROOT / "sources/odd-cycle-results.json").write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: odd-cycle homomorphism hardness audits", flush=True)


if __name__ == "__main__":
    main()
