#!/usr/bin/env python3
"""Generate a one-cell Lean checker from the saved R724 certificate block.

Default mode writes the Lean source. --check verifies the exact JSON input hash,
selected matrices and emitted Lean source without running Lean.
"""
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CERT = ROOT / ".r21-scratch/r724-h1-left-inverse-certificate/evidence/attempt-2-success/certificate.json"
OUT = Path(__file__).with_name("R747JointBlock39Preflight.lean")
CERT_SHA = "d170dc15f81b0aac68da6cb9291e9907ad72e1738cf3a6b6fd7faf9e32a951f4"
P = 2147483647


def render_matrix(rows: list[list[int]]) -> str:
    lines=[]
    for row in rows:
        lines.append("    ![" + ", ".join(f"({x} : M)" for x in row) + "]")
    return "![\n" + ",\n".join(lines) + "\n  ]"


def generated(cert: dict) -> tuple[str, dict]:
    blocks=cert["blocks"]
    block=max(blocks, key=lambda b:b["dimension"])
    assert block["dimension"] == 39
    A=[[x[0] for x in row] for row in block["A"]]
    B=[[x[0] for x in row] for row in block["B"]]
    assert all(len(r)==39 for r in A+B)
    assert all(0 <= x < P for r in A+B for x in r)
    assert all(cell[1:] == [0,0,0] for mat in (block["A"],block["B"]) for row in mat for cell in row)
    counts=[sum(B[i][k] != 0 and A[k][i] != 0 for k in range(39)) for i in range(39)]
    i=max(range(39), key=lambda n: (counts[n], -n))
    assert block["scc_index"] == 6 and i == 28 and counts[i] == 7
    text = f'''/- R747 one-cell kernel preflight.
Generated from the exact R724 certificate JSON. This checks a single diagonal
entry in the largest SCC; it is not a full matrix or privacy proof. -/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace R747JointBlock39Preflight

abbrev M := ZMod {P}

-- SCC {block['scc_index']}; local row/column {i}. Entries are certificate limb 0.
def A : Matrix (Fin 39) (Fin 39) M := {render_matrix(A)}

def B : Matrix (Fin 39) (Fin 39) M := {render_matrix(B)}

theorem selected_cell : (B * A) {i} {i} = 1 := by
  simp only [Matrix.mul_apply, A, B, Fin.sum_univ_succ, Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num
  decide

#print axioms selected_cell

end R747JointBlock39Preflight
'''
    meta={"scc_index":block["scc_index"],"dimension":block["dimension"],"local_diagonal_index":i,
          "rows_original":block["rows_original"],"columns_original":block["columns_original"],
          "nonzero_A":sum(x!=0 for r in A for x in r),"nonzero_B":sum(x!=0 for r in B for x in r),
          "nonzero_diagonal_product_summands":counts[i],"diagonal_candidates":[n for n,c in enumerate(counts) if c==max(counts)]}
    return text,meta


def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args=ap.parse_args()
    raw=CERT.read_bytes()
    h=hashlib.sha256(raw).hexdigest()
    if h != CERT_SHA: raise SystemExit(f"certificate SHA mismatch: {h}")
    cert=json.loads(raw)
    assert cert["modulus"]==P
    text,meta=generated(cert)
    if args.check:
        if not OUT.exists(): raise SystemExit("generated Lean source missing")
        if OUT.read_text()!=text: raise SystemExit("generated Lean source differs from exact certificate input")
        print(f"check=ok certificate_sha256={h} lean_sha256={hashlib.sha256(text.encode()).hexdigest()} metadata={json.dumps(meta,sort_keys=True)}")
    else:
        OUT.write_text(text)
        print(f"wrote={OUT} certificate_sha256={h} lean_sha256={hashlib.sha256(text.encode()).hexdigest()} metadata={json.dumps(meta,sort_keys=True)}")

if __name__ == "__main__": main()
