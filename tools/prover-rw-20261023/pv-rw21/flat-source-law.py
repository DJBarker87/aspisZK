"""Emit only 8 limb reads and 32 byte reads, each using a named symbolic law.
No generated field value, wide recurrence cell, or large decision is reduced.
"""
from pathlib import Path
import sys,hashlib,json
r=Path(__file__).resolve().parents[3]
p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRw21FlatSourceLaw.lean'
s='''import R1Z.ProverRw21FlatLimbs
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21FlatSourceLaw
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw21ArrayRead ProverRw21FlatOutput

theorem exact (x : W) : ProverRwP6FlatSource.wide_bytes_flat x=ok (output x) := by
  unfold ProverRwP6FlatSource.wide_bytes_flat
    ProverRwP6FlatSource.aspis_core.field.wide_exact.WideExact.to_limbs
    ProverRwDictionaryBytes.Src.limbs
    ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.to_limbs
  simp only [bind_tc_ok]
'''
for i in range(8):s+=f'  have hw{i} := ProverRw21FlatLimbs.word{i} x\n  dsimp only [words] at hw{i}\n  rw [hw{i}]\n  simp only [bind_tc_ok,lift]\n'
fields=['c0.c0.a','c0.c0.b','c0.c1.a','c0.c1.b','c1.c0.a','c1.c0.b','c1.c1.a','c1.c1.b']
for f in fields:
 for i in range(4):s+=f'  rw [exact_read (core.num.U32.to_le_bytes x.{f}) {i}#usize (by decide)]\n  simp only [bind_tc_ok,lift]\n'
s+='''  apply congrArg Result.ok
  apply Subtype.ext
  change _=bytes x
  unfold bytes
'''
for f in fields:s+=f'  rw [four (core.num.U32.to_le_bytes x.{f})]\n'
s+='''  rfl

#print axioms exact
end R1Z.ProverRw21FlatSourceLaw
'''
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print(json.dumps(dict(symbolic_limb_reads=8,symbolic_byte_reads=32,decision_carriers='Only bounds on indices 0..7 and 0..3',sha256=hashlib.sha256(s.encode()).hexdigest())))
