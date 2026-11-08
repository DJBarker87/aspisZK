import NNV_PrepareFilled
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_PrepareBufferLengths
open RSL NNH_Libraries

theorem returned (a : TX1_087.Args VL) (env : Env) (sem : Verified VL) (v : VL.View)
 (p : NNV_PrepareFrontCut.Packet a env sem v) :
 p.logical.length=14759 ∧ (p.logical.take LOGICAL_SEMANTIC).length=13831 ∧
 (p.logical.drop LOGICAL_SEMANTIC).length=928 := by
 have len : p.logical.length = LOGICAL_SEMANTIC+LOGICAL_Y1 := by
  rw [(NNV_PrepareFilled.returned a env sem v p).2,List.length_replicate]
 constructor
 · exact len
 constructor
 · rw [List.length_take,len]
 · rw [List.length_drop,len]
#print axioms returned
end AspisR1.NNV_PrepareBufferLengths
end
