"""Regenerate the quotient search and rank certificates, all checked by Lean.

Use --check to require that the committed certificates match regeneration.
This program is outside the proof's trusted base.
"""
import ast
from collections import deque
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[1]
source_path = root / "TreewidthHom/ArrowQuotient.lean"
source = source_path.read_text()
arrow = (root / "TreewidthHom/ArrowSearch.lean").read_text()
edges = ast.literal_eval(re.search(r"^def edges .* := (\[.*\])$", arrow, re.M).group(1))
adj = set(edges) | {(v, u) for u, v in edges}
collapse = lambda v: 8 if v == 10 else v
quotient_adj = {(collapse(u), collapse(v)) for u, v in adj}
states = [[]]
lines = []
for n in range(1, 14):
    states = [xs + [y] for xs in states for y in range(13)
              if all((y, x) in quotient_adj for j, x in enumerate(xs)
                     if (n - 1, j) in adj)]
    lines += [f"private def level{n} : List (List ℕ) := " + repr(states),
              "set_option maxHeartbeats 0 in",
              f"private theorem checkpoint{n} : assignments {n} = level{n} := by",
              f"  rw [assignments{', checkpoint' + str(n - 1) if n > 1 else ''}]",
              "  decide +kernel", ""]
    print(f"level {n}: {len(states)} partial maps")
data = []
for f in states:
    distances, queue = {7: 0}, deque([7])
    while queue:
        v = queue.popleft()
        for u, w in sorted(adj):
            if u == v and f[w] != 8 and w not in distances:
                distances[w] = distances[v] + 1
                queue.append(w)
    assert f[7] != 8
    assert all(v in distances for v in range(13) if f[v] != 8)
    assert all(any((v, u) in adj and f[u] != 8 for u in range(13))
               for v in range(13) if f[v] == 8)
    data.append((f, [distances.get(v, 0) for v in range(13)]))
assert len(data) == 8
start = source.index("private def level1")
end = source.index("/-- Each candidate", start)
updated = source[:start] + "\n".join(lines) + "\n" + source[end:]
updated = re.sub(r"^def certificateData .* := .*?$",
                 "def certificateData : List (List ℕ × List ℕ) := " + repr(data),
                 updated, flags=re.M)
if "--check" in sys.argv:
    assert updated == source, "Certificates differ: regenerate and rebuild Lean."
else:
    source_path.write_text(updated)
print("PASS: eight quotient maps with connectivity certificates")
