import NNV_PrepareFrontCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_PrepareValuesOutput
open RSL NNH_Libraries

theorem returned (a : TX1_087.Args VL) (env : Env) (sem : Verified VL) (v : VL.View)
 (p : NNV_PrepareFrontCut.Packet a env sem v) :
 LIBC_ExpandValues.Good (slice a.proof OFF_Y1 OFF_INACTIVE,p.logical.drop LOGICAL_SEMANTIC) ∧
 p.y1 = LIB_Carriers.bytes (LIBC_ExpandValuesModel.output
  (LIBC_Bytes.raw (slice a.proof OFF_Y1 OFF_INACTIVE))
  (LIBC_Bytes.raw (p.logical.drop LOGICAL_SEMANTIC))) := by
 have called := p.expandedValues
 change LIBC_ExpandValues.value _ env = .ok p.y1 at called
 unfold LIBC_ExpandValues.value at called
 split at called
 · rename_i good
   exact ⟨good,(Except.ok.inj called).symm⟩
 · cases called
#print axioms returned
end AspisR1.NNV_PrepareValuesOutput
end
