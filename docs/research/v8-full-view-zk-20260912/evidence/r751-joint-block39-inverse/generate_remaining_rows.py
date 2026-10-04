#!/usr/bin/env python3
"""Generate the remaining SCC-6 row-check chunks from exact R724 cert data."""
import argparse, hashlib, json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
CERT=ROOT/".r21-scratch/r724-h1-left-inverse-certificate/evidence/attempt-2-success/certificate.json"
DEP747=ROOT/".r21-scratch/r747-joint-block39-preflight/R747JointBlock39Preflight.lean"
DEP749=ROOT/".r21-scratch/r749-joint-block39-row28/R749JointBlock39Row28.lean"
CERT_SHA="d170dc15f81b0aac68da6cb9291e9907ad72e1738cf3a6b6fd7faf9e32a951f4"
DEP747_SHA="0d3d110e4bfc42a5769dd0e5c4c77c4f464f4e7be6c4769644ec84fa6557a78a"
DEP749_SHA="c1c50f7b7f09ea78a13b72a0e8d632dd28728f8ebc1041d1afdb2228b9fa2996"
OUTDIR=Path(__file__).with_name('chunks')
CHUNKS=[[38,0,1,2],[3,4,5,6],[7,8,9,10],[11,12,13,14],[15,16,17,18],[19,20,21,22],[23,24,25,26],[27,29,30,31],[32,33,34,35],[36,37]]

def build(chunk_id,rows,cert):
    b=max(cert['blocks'],key=lambda x:x['dimension'])
    A=[[cell[0] for cell in row] for row in b['A']]
    B=[[cell[0] for cell in row] for row in b['B']]
    assert b['scc_index']==6 and b['dimension']==39
    assert 28 not in rows and all(0<=r<39 for r in rows)
    assert all(cell[1:]==[0,0,0] for key in ('A','B') for row in b[key] for cell in row)
    lines=[f'''/- SCC 6 rows {rows}; exact R724 certificate data. -/
import AspisV8R19.R747JointBlock39Preflight
import Mathlib.Tactic

namespace R750JointBlock39Rows{chunk_id:02d}
open R747JointBlock39Preflight
''']
    for r in rows:
        vals=[sum(B[r][k]*A[k][j] for k in range(39))%2147483647 for j in range(39)]
        assert vals==[int(j==r) for j in range(39)],(r,vals)
        for j,v in enumerate(vals):
            lines.append(f'''theorem cell_{r}_{j} : (B * A) {r} {j} = {v} := by
  simp only [Matrix.mul_apply, A, B, Fin.sum_univ_succ,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num <;> decide
''')
        lines.append(f'''theorem row_{r} : ∀ j : Fin 39,
    (B * A) {r} j = (1 : Matrix (Fin 39) (Fin 39) M) {r} j := by
  intro j
  fin_cases j
''')
        for j in range(39):
            lines.append(f'  · simpa [Matrix.one_apply] using cell_{r}_{j}\n')
        lines.append(f'\n#print axioms row_{r}\n')
    lines.append(f'end R750JointBlock39Rows{chunk_id:02d}\n')
    return ''.join(lines)

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--check',action='store_true'); ap.add_argument('--chunk',type=int,choices=range(len(CHUNKS))); args=ap.parse_args()
    csha=hashlib.sha256(CERT.read_bytes()).hexdigest(); s747=hashlib.sha256(DEP747.read_bytes()).hexdigest(); s749=hashlib.sha256(DEP749.read_bytes()).hexdigest()
    if csha!=CERT_SHA: raise SystemExit(f'certificate SHA mismatch {csha}')
    if s747!=DEP747_SHA: raise SystemExit(f'R747 SHA mismatch {s747}')
    if s749!=DEP749_SHA: raise SystemExit(f'R749 SHA mismatch {s749}')
    cert=json.loads(CERT.read_bytes()); OUTDIR.mkdir(exist_ok=True)
    ids=range(len(CHUNKS)) if args.chunk is None else [args.chunk]
    for idx in ids:
        text=build(idx+1,CHUNKS[idx],cert); p=OUTDIR/f'R750JointBlock39Rows{idx+1:02d}.lean'
        if args.check:
            if not p.exists() or p.read_text()!=text: raise SystemExit(f'generated source mismatch/missing: {p}')
        else: p.write_text(text)
        print(f'{p.name} rows={CHUNKS[idx]} bytes={len(text)} sha256={hashlib.sha256(text.encode()).hexdigest()}')
    print(f'check={"ok" if args.check else "written"} cert={csha} R747={s747} R749={s749} chunks={list(ids)}')
if __name__=='__main__': main()
