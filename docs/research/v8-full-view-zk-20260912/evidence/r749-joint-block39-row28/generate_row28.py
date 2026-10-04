#!/usr/bin/env python3
"""Emit/check the exact 39 scalar row-28 Lean checks for R724 SCC 6."""
import argparse, hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
CERT=ROOT/".r21-scratch/r724-h1-left-inverse-certificate/evidence/attempt-2-success/certificate.json"
DEP=ROOT/".r21-scratch/r747-joint-block39-preflight/R747JointBlock39Preflight.lean"
OUT=Path(__file__).with_name("R749JointBlock39Row28.lean")
CERT_SHA="d170dc15f81b0aac68da6cb9291e9907ad72e1738cf3a6b6fd7faf9e32a951f4"
DEP_SHA="0d3d110e4bfc42a5769dd0e5c4c77c4f464f4e7be6c4769644ec84fa6557a78a"


def build(cert:dict)->tuple[str,list[int]]:
    block=max(cert["blocks"],key=lambda b:b["dimension"])
    assert block["scc_index"]==6 and block["dimension"]==39
    A=[[x[0] for x in row] for row in block["A"]]
    B=[[x[0] for x in row] for row in block["B"]]
    assert all(cell[1:]==[0,0,0] for key in ("A","B") for row in block[key] for cell in row)
    row=[sum(B[28][k]*A[k][j] for k in range(39))%2147483647 for j in range(39)]
    assert row==[int(j==28) for j in range(39)]
    lines=['''/- Row 28 of the exact R724 SCC-6 left-inverse candidate.
The scalar declarations check this row one entry at a time; this file does not
connect the matrix to source execution or prove the full block identity. -/
import AspisV8R19.R747JointBlock39Preflight
import Mathlib.Tactic

namespace R749JointBlock39Row28
open R747JointBlock39Preflight
''']
    for j,v in enumerate(row):
        if j==28:
            lines.append('theorem cell_28 : (B * A) 28 28 = 1 := by\n  exact selected_cell\n')
        else:
            lines.append(f'''theorem cell_{j} : (B * A) 28 {j} = {v} := by
  simp only [Matrix.mul_apply, A, B, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide
''')
    lines.append('theorem row28 : ∀ j : Fin 39,\n    (B * A) 28 j = (1 : Matrix (Fin 39) (Fin 39) M) 28 j := by\n  intro j\n  fin_cases j\n')
    for j in range(39):
        lines.append(f'  · simpa [Matrix.one_apply] using cell_{j}\n')
    lines.append('''
#print axioms row28

end R749JointBlock39Row28
''')
    return ''.join(lines),row


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--check',action='store_true'); args=ap.parse_args()
    ch=hashlib.sha256(CERT.read_bytes()).hexdigest(); dh=hashlib.sha256(DEP.read_bytes()).hexdigest()
    if ch!=CERT_SHA: raise SystemExit(f'certificate SHA mismatch {ch}')
    if dh!=DEP_SHA: raise SystemExit(f'R747 source SHA mismatch {dh}')
    cert=json.loads(CERT.read_bytes()); text,row=build(cert)
    if args.check:
        if not OUT.exists() or OUT.read_text()!=text: raise SystemExit('generated source mismatch/missing')
        print(f'check=ok certificate_sha256={ch} R747_source_sha256={dh} row_sha256={hashlib.sha256(text.encode()).hexdigest()} values={row}')
    else:
        OUT.write_text(text)
        print(f'wrote={OUT} certificate_sha256={ch} R747_source_sha256={dh} row_sha256={hashlib.sha256(text.encode()).hexdigest()} values={row}')
if __name__=='__main__': main()
