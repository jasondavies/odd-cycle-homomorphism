"""Regressions for optimized execution and rejection of invalid certificates."""
from pathlib import Path
import itertools
import json
import subprocess
import sys
import tempfile
import unittest

from check_formalization import audit_output
from list_cycle_hom import (
    Reduction, check_path_decomposition, check_tree_decomposition, hom_to_cycle,
    is_forest_without,
)
from run_list_cycle_checks import girth, verify
from verification import VerificationError

SCRIPTS = Path(__file__).resolve().parent


class VerificationTests(unittest.TestCase):
    def test_treewidth_three_with_full_and_empty_lists(self):
        # Full lists omit the padding assumption: the upper bound still holds.
        for domain in (set(range(5)), set()):
            with self.subTest(domain=domain):
                result = verify([domain], set(), 5)
                self.assertEqual(result["satisfiable"], bool(domain))

    def test_join_minor_and_exact_feedback_number(self):
        for lists, edges, input_fvs in (
                ([{0}, {1}], {(0, 1)}, 0),
                ([{0, 1, 2}]*3, {(0, 1), (0, 2), (1, 2)}, 1)):
            with self.subTest(edges=edges):
                g = Reduction(lists, edges, 5)
                branches = [{v} for v in range(g.m + 2)]
                for boundary, cycle, link, d in g.sweeps:
                    if cycle is not None and d == g.n-1:
                        hub, = boundary
                        self.assertIsNotNone(link)
                        branches[hub].update(cycle[2:])
                        branches[hub].update(link[1:-1])
                    elif cycle is None:
                        branches[min(boundary)].update(link[1:-1])
                assignment = {}
                for i, branch in enumerate(branches):
                    self.assertTrue(branch.isdisjoint(assignment))
                    assignment.update({v: i for v in branch})
                    reached = {next(iter(branch))}
                    while True:
                        more = {v for u, v in g.edges if u in reached and v in branch}
                        more |= {u for u, v in g.edges if v in reached and u in branch}
                        if more <= reached:
                            break
                        reached |= more
                    self.assertEqual(reached, branch)
                quotient = {tuple(sorted((assignment[u], assignment[v])))
                            for u, v in g.edges if u in assignment and v in assignment
                            and assignment[u] != assignment[v]}
                expected = edges | {(g.A, g.B)} | {
                    (v, a) for v in range(g.m) for a in (g.A, g.B)}
                self.assertEqual(quotient, expected)
                # Exhaustively rule out every smaller feedback set in these examples.
                self.assertFalse(any(is_forest_without(g.count, g.edges, removed)
                                     for removed in itertools.combinations(
                                         range(g.count), input_fvs+1)))
                original_set = next(set(s) for s in itertools.combinations(range(g.m), input_fvs)
                                    if is_forest_without(g.m, edges, s))
                self.assertTrue(is_forest_without(g.count, g.edges,
                                                 original_set | {g.A, g.B}))

    def test_forest_completion_all_optimization_modes(self):
        code = """
import json
from list_cycle_hom import hom_to_cycle
from check_formalization import audit_output
from verification import VerificationError
hom, _ = hom_to_cycle(2, {(0, 1)}, 5, core=[])
try:
    audit_output("'test' depends on axioms: [sorryAx]", ["test"], [])
except VerificationError:
    pass
else:
    raise RuntimeError("Optimized audit accepted a proof admission")
print(json.dumps(hom))
"""
        for flags in ([], ["-O"], ["-OO"]):
            with self.subTest(flags=flags):
                result = subprocess.run([sys.executable, *flags, "-c", code],
                                        cwd=SCRIPTS, capture_output=True, text=True, check=True)
                hom = json.loads(result.stdout)
                self.assertEqual(len(hom), 2)
                self.assertIn((hom[0] - hom[1]) % 5, (1, 4))

    def test_invalid_feedback_set_rejected(self):
        with self.assertRaises(VerificationError):
            hom_to_cycle(3, {(0, 1), (1, 2), (0, 2)}, 5, core=[])

    def test_decomposition_edge_and_occurrence_checks(self):
        with self.assertRaises(VerificationError):
            check_path_decomposition(2, {(0, 1)}, [{0}, {1}], 0)
        with self.assertRaises(VerificationError):
            check_tree_decomposition(2, set(), [{0}, {1}, {0}], [(0, 1), (1, 2)], 0)

    def test_decomposition_indices_all_optimization_modes(self):
        code = """
from list_cycle_hom import check_path_decomposition, check_tree_decomposition
from verification import VerificationError

def rejects(check, *args):
    try:
        check(*args)
    except VerificationError:
        return
    raise RuntimeError(f"Accepted invalid decomposition: {args!r}")

for vertex in (-1, 1, 0.0):
    rejects(check_path_decomposition, 1, set(), [{vertex}], 0)
    rejects(check_tree_decomposition, 1, set(), [{vertex}], [], 0)
for edge in ((0, -1), (-1, 0), (0, 2), (2, 0), (0, 1.0)):
    rejects(check_tree_decomposition, 2, set(), [{0}, {1}], [edge], 0)
rejects(check_path_decomposition, 0, set(), [{-1}], 0)
rejects(check_tree_decomposition, 0, set(), [{-1}], [], 0)
rejects(check_path_decomposition, 0, set(), [], 0)
rejects(check_tree_decomposition, 0, set(), [], [], 0)
# The valid boundary identifiers and one empty bag remain accepted.
check_path_decomposition(2, set(), [{0}, {1}], 0)
check_tree_decomposition(2, set(), [{0}, {1}], [(0, 1)], 0)
check_path_decomposition(0, set(), [set()], 0)
check_tree_decomposition(0, set(), [set()], [], 0)
"""
        for flags in ([], ["-O"], ["-OO"]):
            with self.subTest(flags=flags):
                subprocess.run([sys.executable, *flags, "-c", code], cwd=SCRIPTS,
                               capture_output=True, text=True, check=True)

    def test_audit_accepts_exact_standard_output(self):
        result = audit_output("'test' depends on axioms: [propext, Classical.choice, Quot.sound]",
                              ["test"], [])
        self.assertEqual(result["test"], ["propext", "Classical.choice", "Quot.sound"])
        self.assertEqual(audit_output("'test' does not depend on any axioms", ["test"], []),
                         {"test": []})

    def test_audit_rejects_missing_extra_duplicate_and_nonstandard_output(self):
        good = "'test' does not depend on any axioms"
        for output in ("", good + "\n'extra' does not depend on any axioms",
                       good + "\n" + good, "'test' depends on axioms: [sorryAx]",
                       "'test' depends on axioms: [untrustedAxiom]"):
            with self.subTest(output=output), self.assertRaises(VerificationError):
                audit_output(output, ["test"], [])
        for expected in ([], ["test", "test"]):
            with self.subTest(expected=expected), self.assertRaises(VerificationError):
                audit_output(good, expected, [])

    def test_source_admissions_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "Example.lean"
            for declaration in ("theorem bad : True := by sorry", "axiom bad : False",
                                "opaque bad : False", "theorem bad : True := by admit"):
                source.write_text(declaration)
                with self.subTest(declaration=declaration), self.assertRaises(VerificationError):
                    audit_output("'test' does not depend on any axioms", ["test"], [source])

    def test_girth_on_known_graphs(self):
        self.assertIsNone(girth(3, {(0, 1), (1, 2)}))
        self.assertEqual(girth(5, {(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)}), 5)
        # A triangle in a second component must not be missed.
        self.assertEqual(girth(7, {(0, 1), (1, 2), (2, 3), (0, 3),
                                   (4, 5), (5, 6), (4, 6)}), 3)


if __name__ == "__main__":
    unittest.main()
