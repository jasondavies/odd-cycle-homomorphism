"""Cross-check the manuscript algorithms against direct colour assignment."""
import json
import subprocess
import sys
import unittest
from fractions import Fraction
from itertools import combinations
from pathlib import Path
from random import Random

from cycle_algorithms import circular_chromatic_number, circular_clique, long_cycle_homomorphism


def cycle(n):
    return [(v, (v + 1) % n) for v in range(n)]


def direct(order, edges, p, q):
    """Independent circular-clique oracle. Rotation fixes vertex zero."""
    earlier = [[] for _ in range(order)]
    for u, v in edges:
        earlier[max(u, v)].append(min(u, v))
    colours = [0] * order

    def extend(v):
        if v == order:
            return True
        for colour in range(p):
            if all(q <= (colour - colours[u]) % p <= p - q for u in earlier[v]):
                colours[v] = colour
                if extend(v + 1):
                    return True
        return False

    return order == 0 or extend(1)


class CycleAlgorithmTests(unittest.TestCase):
    def check_long(self, order, edges, ell, expected):
        colours = long_cycle_homomorphism(order, edges, ell)
        if not expected:
            self.assertIsNone(colours)
            return
        self.assertIsNotNone(colours)
        self.assertEqual(len(colours), order)
        self.assertTrue(all(0 <= a < ell for a in colours))
        self.assertTrue(all((colours[v] - colours[u]) % ell in (1, ell - 1)
                            for u, v in edges))

    def test_decisions_against_direct_assignments(self):
        graphs = []
        for n in range(5):
            pairs = list(combinations(range(n), 2))
            for mask in range(1 << len(pairs)):
                graphs.append((n, [edge for i, edge in enumerate(pairs) if mask & (1 << i)]))
        rng = Random(173)
        for n in (5, 6, 7):
            for _ in range(25):
                graphs.append((n, [e for e in combinations(range(n), 2) if rng.random() < 0.4]))
        for n, edges in graphs:
            for p, q in ((2, 1), (3, 1), (4, 2), (5, 2), (7, 2), (7, 3), (8, 3)):
                with self.subTest(order=n, edges=edges, p=p, q=q):
                    expected = direct(n, edges, p, q)
                    self.assertEqual(circular_clique(n, edges, p, q), expected)
                    # K_((2q+1)/q) is isomorphic to C_(2q+1).
                    if p == 2 * q + 1:
                        self.check_long(n, edges, p, expected)

    def test_parity_recovery_on_odd_cycles(self):
        # Returning an arbitrary feasible potential can collapse adjacent colours.
        for ell in (5, 7, 13, 31):
            self.check_long(ell, cycle(ell), ell, True)
            self.check_long(ell, list(reversed(cycle(ell))), ell, True)
        # A triangle requires enumeration for ell=3; K4 exhausts those choices.
        self.check_long(3, cycle(3), 3, True)
        self.check_long(4, list(combinations(range(4), 2)), 3, False)

    def test_long_negative_at_matching_odd_girth(self):
        # Three-edge subdivisions of K4 have odd girth nine but cannot map to C9.
        edges = []
        order = 4
        for u, v in combinations(range(4), 2):
            edges.extend(((u, order), (order, order + 1), (order + 1, v)))
            order += 2
        self.check_long(order, edges, 9, False)

    def test_long_components_and_binary_length(self):
        edges = cycle(5) + [(5, 6), (6, 7)]
        self.check_long(9, edges, 5, True)
        huge = 2**256 + 1
        self.check_long(9, edges, huge, False)
        path = [(i, i + 1) for i in range(1200)]
        self.check_long(1202, path, huge, True)

    def test_closed_and_parallel_chains(self):
        # Two cycles meeting at zero compress to two loops at a branch vertex.
        bow_tie = cycle(5) + [(0, 5), (5, 6), (6, 0)]
        self.assertFalse(circular_clique(7, bow_tie, 5, 2))
        self.assertTrue(circular_clique(7, bow_tie, 3, 1))
        # Three internally disjoint paths of lengths 2, 2 and 3 form parallel chains.
        theta = [(0, 2), (2, 1), (0, 3), (3, 1), (0, 4), (4, 5), (5, 1)]
        self.assertTrue(circular_clique(6, theta, 5, 2))
        self.assertFalse(circular_clique(6, theta, 7, 3))
        self.assertEqual(circular_chromatic_number(6, theta), Fraction(5, 2))

    def test_binary_threshold_and_exact_number(self):
        scale = 1 << 256
        for edges, order in ((cycle(5), 5),
                             ([(0, 2), (2, 1), (0, 3), (3, 1), (0, 4), (4, 5), (5, 1)], 6)):
            self.assertTrue(circular_clique(order, edges, 5 * scale, 2 * scale))
            self.assertFalse(circular_clique(order, edges, 5 * scale - 1, 2 * scale))
        disconnected = cycle(5) + [(u + 5, v + 5) for u, v in cycle(7)] + [(11, 12)]
        self.assertEqual(circular_chromatic_number(14, iter(disconnected)), Fraction(5, 2))
        self.assertEqual(circular_chromatic_number(7, cycle(7)), Fraction(7, 3))
        self.assertEqual(circular_chromatic_number(0, []), 0)
        self.assertEqual(circular_chromatic_number(3, []), 1)
        self.assertEqual(circular_chromatic_number(5, [(2, 4)]), 2)
        self.assertEqual(circular_chromatic_number(4, combinations(range(4), 2)), 4)

    def test_cli(self):
        script = Path(__file__).with_name("cycle_algorithms.py")
        graph = json.dumps({"order": 5, "edges": cycle(5)})
        for args, expected in ((["circular-number"], "5/2"), (["circular-clique", "7", "3"], False)):
            run = subprocess.run([sys.executable, script, *args], input=graph, text=True,
                                 capture_output=True, check=True)
            self.assertEqual(json.loads(run.stdout), expected)
        run = subprocess.run([sys.executable, script, "long-cycle", "5"], input=graph,
                             text=True, capture_output=True, check=True)
        colours = json.loads(run.stdout)
        self.assertTrue(all((colours[u] - colours[v]) % 5 in (1, 4) for u, v in cycle(5)))
