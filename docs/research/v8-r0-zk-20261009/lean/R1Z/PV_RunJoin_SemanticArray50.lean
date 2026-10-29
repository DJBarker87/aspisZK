import R1Z.PV_RunJoin_SemanticScalar50
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SemanticArray50
open Aeneas Aeneas.Std ProverRwFull
open ProverCommitPrimitive47

def raw (size : Usize) (a : Array aspis_core.field.QM31 size) (j : Nat) : Old.Q :=
  if h : j<size.val then PV_RunJoin_SemanticScalar50.raw (a.val[j]'(by rw [a.property];exact h))
  else ProverCommitSubfieldOps47.zero

theorem cell (size : Usize) (a : Array aspis_core.field.QM31 size) (j : Fin size.val) :
    ProverRwDictionaryTower.fromQ (ProverCommitNativeQ48.source (raw size a j.val))=
      a.val[j.val]'(by rw [a.property];exact j.isLt) := by
  rw [raw,dif_pos j.isLt,PV_RunJoin_SemanticScalar50.source]

theorem complete (size : Usize) (a : Array aspis_core.field.QM31 size) :
    PV_B2_F_ConstructorCarrier.amap ProverRwDictionaryTower.fromQ
      (ProverCommitQArray48.array size (raw size a))=a := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [PV_B2_F_ConstructorCarrier.amap,ProverCommitQArray48.array,List.length_map,List.length_ofFn,a.property]
  · intro j hj hk
    simp only [PV_B2_F_ConstructorCarrier.amap,ProverCommitQArray48.array,List.getElem_map,List.getElem_ofFn]
    exact cell size a ⟨j,by rw [a.property] at hk;exact hk⟩
#print axioms raw
#print axioms cell
#print axioms complete
end R1Z.PV_RunJoin_SemanticArray50
