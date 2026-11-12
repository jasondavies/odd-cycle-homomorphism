"""Exercise the verified Lean constructor and validate its exported graph encoding.
Finite tests check execution/serialization; compile_spec proves general correctness.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
PRIMES = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67]
# Enumeration order: domain, then each relation's tuple and argument-port tags.
WEIGHTS = [sum(PRIMES[1:3])] + [sum(PRIMES[3+3*i:6+3*i]) for i in range(5)]

def expected(words, ell):
    k, total = len(words), sum(map(len, words))
    if not words or ell == 0:
        return (1, 0), (1, 0)
    if any(len(w) < ell for w in words):
        return (2, 1), (1, 0)
    # Independent counts from the six relational families; N is TOTAL length.
    source_domain = k+1+k*(ell*(total+1)+1)+ell
    target_domain = k+1+sum(len(w)+1 for w in words)+2
    qfacts = [1, k, k, k*ell*total, k*ell, k*ell]
    tfacts = [1, k, k, sum(2*len(w)+1 for w in words), total, total]
    def graph_counts(domain, facts):
        decorated = 3*domain + sum(a*b for a,b in zip(WEIGHTS, facts))
        incidence_arcs = 2*(facts[0]+2*sum(facts[1:]))
        arcs = decorated+incidence_arcs
        return decorated+11*arcs, 30*arcs
    return graph_counts(source_domain, qfacts), graph_counts(target_domain, tfacts)

cases = [([], 3), ([""], 0), ([""], 1), (["0"], 2**256),
         (["0"], 1), (["0", "1"], 1)]
results = []
for words, ell in cases:
    start = time.monotonic()
    proc = subprocess.run(["lake", "env", "lean", "--run", "ReduceLCS.lean", "--json",
                           str(ell), *words], cwd=ROOT, capture_output=True, text=True,
                          check=True, timeout=60)
    data = json.loads(proc.stdout)
    for name, counts in zip(("source", "target"), expected(words, ell)):
        graph = data[name]
        assert (graph["vertices"], len(graph["edges"])) == counts, (words, ell, name, counts)
        edges = set(map(tuple, graph["edges"]))
        assert len(edges) == len(graph["edges"]), "duplicate stored arcs"
        assert all(0 <= u < graph["vertices"] and 0 <= v < graph["vertices"] and u != v
                   for u,v in edges)
        # Fixed no-instance stores a single undirected edge. Raw outputs are symmetric.
        if len(edges) > 1:
            assert all((v,u) in edges for u,v in edges)
        assert graph["vertices"] <= 10**12*(len(words)+sum(map(len,words))+2)**12
    results.append({"words": words, "length": str(ell),
                    "counts": {name: [g["vertices"], len(g["edges"])] for name,g in data.items()},
                    "seconds": round(time.monotonic()-start,3),
                    "output_sha256": hashlib.sha256(proc.stdout.encode()).hexdigest()})
    print("PASS", words, str(ell), results[-1]["counts"], flush=True)

bad = subprocess.run(["lake", "env", "lean", "--run", "ReduceLCS.lean", "1", "02"],
                     cwd=ROOT, capture_output=True, text=True, timeout=30)
assert bad.returncode == 2 and "only 0 and 1" in bad.stderr
report = {"passed": True, "cases": results, "invalid_input_rejected": True,
          "scope": "Executable and encoding regressions, not a runtime-complexity proof."}
(ROOT/"sources/executable-verification.json").write_text(json.dumps(report, indent=2)+"\n")
print("PASS: 6 exported graph-pair checks and invalid-input rejection.")
