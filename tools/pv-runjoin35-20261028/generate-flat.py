from pathlib import Path
R=Path(__file__).resolve().parents[2]
p=R/'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_FlatBytes35.lean'
limbs=['x.c0.c0.a','x.c0.c0.b','x.c0.c1.a','x.c0.c1.b','x.c1.c0.a','x.c1.c0.b','x.c1.c1.a','x.c1.c1.b']
s='''import R1Z.ProverRwP6BodyCandidate
import R1Z.ProverCommitArrayIndex25
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FlatBytes35
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Wide := aspis_core.field.wide_exact.WideExact

def byte (word : U32) (j : Fin 4) : U8 :=
  (core.num.U32.to_le_bytes word).val[j.val]'(by
    rw [(core.num.U32.to_le_bytes word).property];exact j.isLt)

/-- Independent eight-limb/four-byte wire order; every limb is retained. -/
def wire (x : Wide) : Array U8 32#usize :=
  Array.make 32#usize [
'''
s+=',\n'.join('    '+', '.join('byte '+l+' ⟨'+str(j)+',by decide⟩' for j in range(4)) for l in limbs)
s+='''
  ]

/-- Literal flat reference Result, proved by 40 bounded symbolic array
reads. No BitVec byte arithmetic or large recurrence is kernel-evaluated.
Native/reference association remains a separate deployed P obligation. -/
theorem encode (x : Wide) : ProverRwP6FlatSource.wide_bytes_flat x = .ok (wire x) := by
  unfold ProverRwP6FlatSource.wide_bytes_flat
    ProverRwP6FlatSource.aspis_core.field.wide_exact.WideExact.to_limbs
    ProverRwDictionaryBytes.Src.limbs
    ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.to_limbs
  simp only [bind_tc_ok,lift]
'''
for i in range(40):
 s+='  rw [ProverCommitArrayIndex25.array_index_usize_ok _ _ (by decide)]\n  simp only [bind_tc_ok,lift]\n'
s+='''  rfl

variable [ExternalTypes]
theorem installed (ops : ExternalFuns) (x : Wide) :
    (ProverRwP6BodyCandidate.selected ops).op51 x = .ok (wire x) := by
  change ProverRwP6FlatSource.wide_bytes_flat x = _
  exact encode x

#print axioms encode
#print axioms installed
end R1Z.PV_RunJoin_FlatBytes35
'''
if __import__('sys').argv[1:] == ['--check']:
 assert p.read_text()==s, 'flat serializer proof generator drift'
 print('flat serializer proof generator matches committed source')
else:
 p.write_text(s)
