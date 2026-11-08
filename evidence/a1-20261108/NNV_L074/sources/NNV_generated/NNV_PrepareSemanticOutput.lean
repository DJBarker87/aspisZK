import NNV_PrepareFrontCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_PrepareSemanticOutput
open RSL NNH_Libraries

theorem returned (a : TX1_087.Args VL) (env : Env) (sem : Verified VL) (v : VL.View)
 (p : NNV_PrepareFrontCut.Packet a env sem v) :
 p.semantic=LIB_Carriers.bytes (LIBC_ExpandSemanticModel.output
  (LIBC_Bytes.raw (slice a.proof OFF_SEMANTIC OFF_Y1))) := by
 exact (Except.ok.inj p.expandedSemantic).symm

theorem length (a : TX1_087.Args VL) (env : Env) (sem : Verified VL) (v : VL.View)
 (p : NNV_PrepareFrontCut.Packet a env sem v) : p.semantic.length=13831 := by
 rw [returned a env sem v p]
 exact LIBC_ExpandSemantic.output_length _
#print axioms returned
#print axioms length
end AspisR1.NNV_PrepareSemanticOutput
end
