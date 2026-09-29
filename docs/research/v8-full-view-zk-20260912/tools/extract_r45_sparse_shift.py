#!/usr/bin/env python3
"""Reuse the retained generic carry proof with the focused natural-basis import.

Declaration text is copied verbatim. Only imports/namespace and audits differ.
No width-48 conversion code, old matrix certificates, or new premises are used.
"""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
src=repo/'AspisFormal/AspisFormal/V5GoodGateSparseShift.lean';text=src.read_text()
start=text.index('/-- Number of consecutive low one-bits.')
end=text.index('/-- Embed source indices')
start2=text.index('omit [NeZero (2 : K)] in\n@[simp] theorem dyadic_zero')
end2=text.index('omit [NeZero (2 : K)] in\ntheorem sparseBasisPolynomial_eq_sparseFormula')
body=text[start:end]+text[start2:end2]
names=re.findall(r'\btheorem (\w+)',body)
digest=hashlib.sha256(src.read_bytes()).hexdigest()
out=f'''/- Retained symbolic proof from V5GoodGateSparseShift.lean
SHA256 {digest}. See extract_r45_sparse_shift.py. -/
import AspisV8R16.NaturalBasisCore
import Mathlib.Tactic.Ring
namespace AspisR19.RetainedSparseShift
open Matrix Polynomial Polynomial.Chebyshev AspisCircleTensorBinding
variable {{K : Type*}} [Field K] [NeZero (2 : K)]
'''+body+'\n'+''.join(f'#print axioms {n}\n'for n in names)+'end AspisR19.RetainedSparseShift\n'
dest=root/'lean/AspisV8R19/RetainedSparseShift.lean'
if a.check:assert dest.read_text()==out
else:dest.write_text(out)
print(json.dumps({'status':'PASS','mode':'check'if a.check else'write',
    'source_sha256':digest,'retained_theorems':len(names),'declarations':names}))
