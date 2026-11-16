"""Regressions for optimized execution and rejection of invalid certificates."""
from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest

from check_formalization import audit_output
from list_cycle_hom import check_path_decomposition, check_tree_decomposition, hom_to_cycle
from run_list_cycle_checks import girth
from verification import VerificationError

SCRIPTS = Path(__file__).resolve().parent


class VerificationTests(unittest.TestCase):
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
