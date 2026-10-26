"""Generate nominal field codecs; no extracted definition is rewritten."""
from pathlib import Path
import sys,re
root=Path(__file__).resolve().parents[2]
n=sys.argv[1]
p=root/f'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_CB_Op{n}Types.lean'
s=p.read_text()
assert 'structure aspis_core.field.CM31 where' in s
assert 'structure aspis_core.field.QM31 where' in s
haswide='structure aspis_core.field.wide_exact.WideExact where' in s
out=f'''import R1Z.PV_CB_Op{n}Types
import R1Z.ProverRwFullExternalFuns
set_option autoImplicit false
namespace R1Z.PV_CB_Op{n}Transport
abbrev N := ProverRwFull.aspis_core.field.QM31
abbrev C := ProverRwFull.aspis_core.field.CM31
abbrev R := PV_CB_ShippedOp{n}.aspis_core.field.QM31
abbrev RC := PV_CB_ShippedOp{n}.aspis_core.field.CM31
def encodeC (x : C) : RC := ⟨x.a,x.b⟩
def decodeC (x : RC) : C := ⟨x.a,x.b⟩
def encode (x : N) : R := ⟨encodeC x.c0,encodeC x.c1⟩
def decode (x : R) : N := ⟨decodeC x.c0,decodeC x.c1⟩
theorem native_roundtrip (x : N) : decode (encode x) = x := by cases x; rfl
theorem extracted_roundtrip (x : R) : encode (decode x) = x := by cases x; rfl
#print axioms native_roundtrip
#print axioms extracted_roundtrip
'''
if haswide:
 out+=f'''abbrev W := ProverRwFull.aspis_core.field.wide_exact.WideExact
abbrev RW := PV_CB_ShippedOp{n}.aspis_core.field.wide_exact.WideExact
def encodeW (x : W) : RW := ⟨encode x.c0,encode x.c1⟩
def decodeW (x : RW) : W := ⟨decode x.c0,decode x.c1⟩
theorem native_wide_roundtrip (x : W) : decodeW (encodeW x) = x := by cases x; rfl
theorem extracted_wide_roundtrip (x : RW) : encodeW (decodeW x) = x := by cases x; rfl
#print axioms native_wide_roundtrip
#print axioms extracted_wide_roundtrip
'''
out+=f'end R1Z.PV_CB_Op{n}Transport\n'
p.with_name(f'PV_CB_Op{n}Transport.lean').write_text(out)
