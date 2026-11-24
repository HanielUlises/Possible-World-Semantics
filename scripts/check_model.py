#!/usr/bin/env python3
"""Check that Model/Satisfiable.lean models the current axioms.

For every `axiom` in Grounding/, Modality/ and Situation/:
  * if the model proves a `theorem` of the same name, its statement must
    match the axiom's statement exactly (up to whitespace);
  * otherwise the axiom must be a primitive (a type, relation or
    constant) and the model must define something of the same name.
Every defined notion and notation the axioms depend on must also be
copied into the model verbatim.

Exits non-zero, listing every problem, if any check fails.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCE_DIRS = ["Grounding", "Modality", "Situation"]
MODEL = ROOT / "Model" / "Satisfiable.lean"

# Definitions that occur in axiom statements or in the model's
# non-degeneracy results, and must therefore match the development.
COPIED_DEFS = [
    "R", "Box", "Diamond", "OrdinaryObject", "AbstractObject", "Object",
    "Situation", "PartOf", "Agree", "ExtEq", "actualWorld", "Actual",
    "Possible", "Worldhood", "Maximal₁", "Partial₁", "Consistent",
    "Actually", "AllConcrete", "EverythingActuallyConcrete",
    "Barcan", "ConverseBarcan",
]

# Notations that occur in axiom statements.
NOTATION_RE = re.compile(r"^(notation|infixl|infixr)\b.*=>\s*(\w+)\b.*$")
NOTATION_TARGETS = {
    "TrueIn", "neg", "conj", "disj", "impl", "Box", "Diamond",
    "OrdinaryObject", "AbstractObject", "PartOf", "Actually",
}


def norm(text: str) -> str:
    return " ".join(text.split())


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def blocks(text: str):
    """Split into top-level declaration blocks (a block ends at a blank line)."""
    return [b.strip() for b in re.split(r"\n\s*\n", strip_comments(text)) if b.strip()]


def axioms():
    found = {}
    for d in SOURCE_DIRS:
        for f in sorted((ROOT / d).glob("*.lean")):
            for b in blocks(f.read_text()):
                m = re.match(r"axiom\s+(\S+)\s*:\s*(.*)", b, re.S)
                if m:
                    found[m.group(1)] = (norm(m.group(2)), f.relative_to(ROOT))
    return found


def source_defs_and_notations():
    defs, notations = {}, set()
    for d in SOURCE_DIRS:
        for f in sorted((ROOT / d).glob("*.lean")):
            text = strip_comments(f.read_text())
            for b in blocks(text):
                m = re.match(r"(?:noncomputable\s+)?def\s+(\S+)", b)
                if m:
                    defs[m.group(1)] = norm(b)
            for line in text.splitlines():
                m = NOTATION_RE.match(line.strip())
                if m and m.group(2) in NOTATION_TARGETS:
                    notations.add(norm(line))
    return defs, notations


def main() -> int:
    model_text = strip_comments(MODEL.read_text())
    model_blocks = blocks(model_text)
    theorems, defined, model_defs = {}, set(), {}
    for b in model_blocks:
        m = re.match(r"theorem\s+(\S+)\s*:\s*(.*?)\s*:=", b, re.S)
        if m:
            theorems[m.group(1)] = norm(m.group(2))
        m = re.match(r"(?:noncomputable\s+)?(?:def|abbrev|inductive|structure)\s+(\S+)", b)
        if m:
            defined.add(m.group(1))
            model_defs[m.group(1)] = norm(b)
    model_notations = {norm(l) for l in model_text.splitlines()
                       if NOTATION_RE.match(l.strip())}

    problems = []
    ax = axioms()
    for name, (stmt, path) in ax.items():
        if name in theorems:
            if theorems[name] != stmt:
                problems.append(f"{name} ({path}): statement differs\n"
                                f"    axiom: {stmt}\n    model: {theorems[name]}")
        elif name not in defined:
            problems.append(f"{name} ({path}): not modelled")
        elif stmt.startswith("∀") or "↔" in stmt or "∧" in stmt:
            problems.append(f"{name} ({path}): is a proposition but the model "
                            "only defines it; it must be proved as a theorem")

    src_defs, src_notations = source_defs_and_notations()
    for name in COPIED_DEFS:
        if name not in src_defs:
            problems.append(f"def {name}: missing from the development")
        elif model_defs.get(name) != src_defs[name]:
            problems.append(f"def {name}: model copy differs\n"
                            f"    source: {src_defs[name]}\n"
                            f"    model:  {model_defs.get(name)}")
    for n in sorted(src_notations - model_notations):
        problems.append(f"notation missing from model: {n}")

    if problems:
        print("Model check FAILED:")
        for p in problems:
            print("  - " + p)
        return 1
    n_thm = sum(1 for a in ax if a in theorems)
    print(f"Model check passed: {len(ax)} axioms "
          f"({n_thm} proved, {len(ax) - n_thm} primitives defined), "
          f"{len(COPIED_DEFS)} definitions and {len(src_notations)} notations match.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
