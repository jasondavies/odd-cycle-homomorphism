"""Regenerate finite search checkpoints; Lean checks every equality independently.

This generator is not part of the proof's trusted base. A wrong checkpoint
causes the kernel-checked computation to fail.
"""
import ast
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
path = root / "TreewidthHom/ArrowSearch.lean"
source = path.read_text()
edge_text = re.search(r"^def edges .* := (\[.*\])$", source, re.M).group(1)
edges = ast.literal_eval(edge_text)
adjacency = set(edges) | {(v, u) for u, v in edges}
states = [[]]
lines = ["-- Concrete checkpoints keep kernel normalization from recomputing earlier levels.\n"]
for n in range(1, 14):
    states = [xs + [y] for xs in states for y in range(13)
              if all((y, x) in adjacency for j, x in enumerate(xs)
                     if (n - 1, j) in adjacency)]
    lines += [f"private def level{n} : List (List ℕ) := " + repr(states),
              "set_option maxRecDepth 100000 in",
              "set_option maxHeartbeats 0 in",
              f"private theorem checkpoint{n} : assignments {n} = level{n} := by",
              f"  rw [assignments{', checkpoint' + str(n - 1) if n > 1 else ''}]",
              "  decide +kernel", ""]
    print(f"level {n}: {len(states)} partial maps")
assert states == [list(range(13))]
start = source.index("-- Concrete checkpoints")
end = source.index("/-- Exhaustive evaluation", start)
path.write_text(source[:start] + "\n".join(lines) + "\n" + source[end:])
