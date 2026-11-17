"""Build and audit the principal Lean declarations; reject nonstandard axioms."""
from pathlib import Path
import json
import re
import subprocess

from verification import require

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def audit_output(output, expected, sources):
    """Validate compiler output and source admissions before creating a report."""
    entries = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", output)
    empty = re.findall(r"'([^']+)' does not depend on any axioms", output)
    names = [name for name, _ in entries] + empty
    require(bool(expected), "No declarations requested for the axiom audit")
    require(len(expected) == len(set(expected)), "Duplicate requested declarations")
    require(len(names) == len(set(names)), "Duplicate declarations in audit output")
    require(set(names) == set(expected),
            f"Audit declaration mismatch: expected {sorted(expected)}, found {sorted(names)}")
    require("sorryAx" not in output, "Proof admission found in audit output")
    axioms = {}
    for name, values in entries:
        used = [s.strip() for s in values.split(",") if s.strip()]
        require(set(used) <= ALLOWED_AXIOMS,
                f"Nonstandard axioms for {name}: {sorted(set(used) - ALLOWED_AXIOMS)}")
        axioms[name] = used
    axioms.update({name: [] for name in empty})
    for source in sources:
        require(not re.search(r"^\s*(?:axiom\s|opaque\s)|\b(?:sorry|admit)\b",
                              source.read_text(), re.M),
                f"Proof admission or unverified declaration in {source}")
    return axioms


def project_state(root):
    def git(*args):
        return subprocess.check_output(["git", *args], cwd=root, text=True).strip()
    revision = git("rev-parse", "HEAD")
    # Keep porcelain status prefixes intact, including leading spaces.
    status = subprocess.check_output(
        ["git", "status", "--porcelain=v1", "--untracked-files=all"],
        cwd=root, text=True).splitlines()
    return {"project_commit": revision, "working_tree_dirty": bool(status),
            "working_tree_status": status}


def main():
    provenance = project_state(ROOT)
    subprocess.run(["lake", "build"], cwd=ROOT, check=True)
    result = subprocess.run(["lake", "env", "lean", "AxiomAudit.lean"], cwd=ROOT,
                            check=True, text=True, capture_output=True)
    print(result.stdout, end="")
    expected = re.findall(r"^#print axioms (\S+)",
                          (ROOT / "AxiomAudit.lean").read_text(), re.M)
    sources = [ROOT / "TreewidthHom.lean", ROOT / "Solution.lean", ROOT / "AxiomAudit.lean", *sorted((ROOT / "TreewidthHom").rglob("*.lean"))]
    axioms = audit_output(result.stdout, expected, sources)
    require(project_state(ROOT) == provenance, "Working-tree status changed during the audit")
    report = {
        **provenance,
        "provenance_note": "Git state sampled before verification; dirty paths are relative to the repository root.",
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "mathlib_commit": next(p["rev"] for p in json.loads(
            (ROOT / "lake-manifest.json").read_text())["packages"] if p["name"] == "mathlib"),
        "theorems_audited": expected,
        "axioms": axioms,
        "build_passed": True,
        "scope": "List Colouring to homomorphism into an input odd cycle. ListReduction.reduction checks decision equivalence, source treewidth max(w+2,3), source pathwidth p+6, target pathwidth 2, feedback vertex set transfer of size |S|+2, and polynomial source size. parameter_reduction adds numerical parameter bounds, degeneracy, girth, connectedness under omitted-colour hypotheses, and an edge bound. Odd closed-walk length and palette-padding lemmas are checked, as are the bag and forest extension criteria. The join minor, matching treewidth and feedback-number bounds, pathwidth lower bound, target-capping equivalence, and odd-cycle-core finite reduction are checked. The library also proves odd-cycle-core recognition equivalent to mapping to a shortest odd cycle. Finite-index tree certificates preserve width on finite graphs. Output tree and path bag counts are polynomial in numeric m,n and the supplied input bag count. Bit-level encodings, palette compaction, circular chromatic number, external hardness, and machine resource bounds (including transducer implementation) remain outside Lean.",
    }
    (ROOT / "reports").mkdir(exist_ok=True)
    (ROOT / "reports/lean-verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS: {len(expected)} theorem axiom audits; no proof admissions.")


if __name__ == "__main__":
    main()
