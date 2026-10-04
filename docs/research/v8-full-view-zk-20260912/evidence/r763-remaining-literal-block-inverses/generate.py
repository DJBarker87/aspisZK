#!/usr/bin/env python3
"""Emit bounded Lean checks for non-SCC-6 blocks in the R724 certificate.

This only formats the previously checked certificate.  It deliberately does
not multiply matrices, invert blocks, or perform finite-field elimination.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CERT = ROOT / ".r21-scratch/r724-h1-left-inverse-certificate/evidence/attempt-2-success/certificate.json"
OUT = Path(__file__).with_name("generated")
EXPECTED_CERT_SHA = "d170dc15f81b0aac68da6cb9291e9907ad72e1738cf3a6b6fd7faf9e32a951f4"
EXPECTED_INPUT_SHA = "91d9b576b357943c0818c460e4f491ddf94e189a133b6c6cce20704c633e72af"
PRIME = 2147483647


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_cert() -> dict:
    raw = CERT.read_bytes()
    if sha(raw) != EXPECTED_CERT_SHA:
        raise SystemExit(f"certificate SHA mismatch: {sha(raw)}")
    d = json.loads(raw)
    if d["input_matrix_sha256_expected"] != EXPECTED_INPUT_SHA:
        raise SystemExit("certificate original-matrix SHA mismatch")
    if d["modulus"] != PRIME or d["rows"] != 222:
        raise SystemExit("unexpected certificate field/dimension")
    return d


def scalar(cell: list[int]) -> int:
    if len(cell) != 4 or cell[1:] != [0, 0, 0]:
        raise SystemExit(f"expected scalar-only certificate cell, got {cell}")
    if not 0 <= cell[0] < PRIME:
        raise SystemExit(f"M31 limb out of range: {cell[0]}")
    return cell[0]


def vec(values: list[list[int]]) -> str:
    return "![" + ", ".join(f"({scalar(v)} : M)" for v in values) + "]"


def matrix(name: str, n: int, rows: list[list[int]]) -> str:
    if len(rows) != n or any(len(r) != n for r in rows):
        raise ValueError(f"{name}: bad square matrix dimensions")
    return "def " + name + " : Matrix (Fin " + str(n) + ") (Fin " + str(n) + ") M := ![\n" + ",\n".join("  " + vec(r) for r in rows) + "\n]\n"


def matrix_file(block: dict) -> str:
    idx, n = block["scc_index"], block["dimension"]
    ns = f"R752SCC{idx:02d}Matrix"
    return (
        f"/- Literal matrices from R724 certificate SCC {idx}; generated without recomputing products. -/\n"
        "import Mathlib.Data.Matrix.Basic\n"
        "import Mathlib.Data.Fin.VecNotation\n"
        "import Mathlib.Data.ZMod.Basic\n\n"
        f"namespace {ns}\nabbrev M := ZMod {PRIME}\n\n"
        + matrix("A_scc", n, block["A"])
        + "\n"
        + matrix("B_scc", n, block["B"])
        + f"\nend {ns}\n"
    )


def cell_tactic() -> str:
    return "  simp only [Matrix.mul_apply, A_scc, B_scc, Fin.sum_univ_succ,\n    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]\n  norm_num <;> decide\n"


def row_chunk_file(block: dict, group: list[int], chunk_no: int) -> str:
    idx, n = block["scc_index"], block["dimension"]
    ns = f"R752SCC{idx:02d}Rows{chunk_no:02d}"
    matrix_ns = f"R752SCC{idx:02d}Matrix"
    lines = [
        f"/- SCC {idx}, rows {group}; each scalar product is checked independently. -/",
        f"import AspisV8R19.{matrix_ns}",
        "import Mathlib.Tactic",
        "",
        f"namespace {ns}",
        f"open {matrix_ns}",
        "",
    ]
    identity = block["B_times_A"]
    for r in group:
        for c in range(n):
            rhs = "1" if r == c else "0"
            # The supplied optimized Rust certificate already checked B*A;
            # this guard only verifies the serialized expected identity.
            expected_limbs = [1, 0, 0, 0] if r == c else [0, 0, 0, 0]
            if identity[r][c] != expected_limbs:
                raise SystemExit(f"certificate B_times_A is not identity at SCC {idx} ({r},{c})")
            lines.extend([
                f"theorem cell_{r}_{c} : (B_scc * A_scc) ({r} : Fin {n}) ({c} : Fin {n}) = ({rhs} : M) := by",
                cell_tactic().rstrip(),
                "",
            ])
        lines.extend([
            f"theorem row_{r} : ∀ j, (B_scc * A_scc) ({r} : Fin {n}) j = if ({r} : Fin {n}) = j then (1 : M) else 0 := by",
            "  intro j",
            "  fin_cases j",
        ])
        for c in range(n):
            lines.extend([f"  · simpa using cell_{r}_{c}"])
        lines.extend([f"#print axioms row_{r}", ""])
    lines.append(f"end {ns}")
    lines.append("")
    return "\n".join(lines)


def aggregate_file(block: dict, chunk_count: int) -> str:
    idx, n = block["scc_index"], block["dimension"]
    matrix_ns = f"R752SCC{idx:02d}Matrix"
    chunks = [f"R752SCC{idx:02d}Rows{k:02d}" for k in range(1, chunk_count + 1)]
    ns = f"R752SCC{idx:02d}Inverse"
    imports = [f"AspisV8R19.{matrix_ns}", *[f"AspisV8R19.{x}" for x in chunks], "Mathlib.LinearAlgebra.Matrix.NonsingularInverse"]
    lines = [f"import {x}" for x in imports]
    lines += ["", f"namespace {ns}", f"open {matrix_ns}", "", f"local instance : Fact (1 < {PRIME}) := ⟨by decide⟩", ""]
    lines += ["theorem left_inverse : B_scc * A_scc = 1 := by", "  ext i j", "  fin_cases i"]
    for r in range(n):
        group_no = r // 4 + 1
        row_ns = f"R752SCC{idx:02d}Rows{group_no:02d}"
        lines.append("  · fin_cases j")
        for c in range(n):
            lines.append(f"    · simpa [Matrix.one_apply] using {row_ns}.cell_{r}_{c}")
    lines += [
        "theorem determinant_isUnit : IsUnit (Matrix.det A_scc) :=",
        "  Matrix.isUnit_det_of_left_inverse left_inverse",
        "",
        "#print axioms determinant_isUnit",
        "",
        "#print axioms left_inverse",
        "",
        "theorem determinant_nonzero : Matrix.det A_scc ≠ 0 :=",
        "  Matrix.det_ne_zero_of_left_left_inverse left_inverse".replace("det_ne_zero_of_left_left_inverse", "det_ne_zero_of_left_inverse"),
        "",
        "#print axioms determinant_nonzero",
        "",
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def outputs(d: dict) -> dict[Path, str]:
    result: dict[Path, str] = {}
    for block in d["blocks"]:
        idx = block["scc_index"]
        if idx == 6:
            continue
        n = block["dimension"]
        ddir = OUT / f"scc-{idx:02d}"
        result[ddir / f"R752SCC{idx:02d}Matrix.lean"] = matrix_file(block)
        groups = [list(range(s, min(s + 4, n))) for s in range(0, n, 4)]
        for k, group in enumerate(groups, 1):
            result[ddir / f"R752SCC{idx:02d}Rows{k:02d}.lean"] = row_chunk_file(block, group, k)
        result[ddir / f"R752SCC{idx:02d}Inverse.lean"] = aggregate_file(block, len(groups))
    return result


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    d = load_cert()
    files = outputs(d)
    if args.check:
        missing = [str(p) for p in files if not p.exists()]
        extra = [str(p) for p in OUT.rglob("*.lean") if p not in files]
        mismatched = [str(p) for p, text in files.items() if p.exists() and p.read_text() != text]
        if missing or extra or mismatched:
            raise SystemExit(f"check failed missing={missing} extra={extra} mismatched={mismatched}")
    else:
        for p, text in files.items():
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
    dims = [b["dimension"] for b in d["blocks"] if b["scc_index"] != 6]
    total_entries = sum(x * x for x in dims)
    n_chunks = sum((x + 3) // 4 for x in dims)
    print(f"check={'ok' if args.check else 'written'} blocks={len(dims)} max_dim={max(dims)} diagonal_entries={total_entries} row_chunks={n_chunks} certificate_sha256={EXPECTED_CERT_SHA}")


if __name__ == "__main__":
    main()
