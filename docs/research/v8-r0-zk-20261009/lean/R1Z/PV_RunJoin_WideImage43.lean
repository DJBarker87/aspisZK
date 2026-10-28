import R1Z.PV_RunJoin_WidePoint43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WideImage43
open Aeneas Aeneas.Std ProverRwFull
open ProverCommitPrimitive47 ProverCommitSubfieldOps47 ProverCommitWideOps48
open AspisR1.RetainedFieldByteCodec
abbrev W := aspis_core.field.wide_exact.WideExact

def source (q : Raw) : W := PV_RunJoin_WidePoint43.source q
def byte (b : U8) : UInt8 := PV_RunJoin_WidePoint43.byte b

theorem point (q : Raw) (hq : canonical q) (i : Fin 32) :
    byte ((PV_RunJoin_FlatBytes35.wire (source q)).val[i.val]'(by
      rw [(PV_RunJoin_FlatBytes35.wire _).property];exact i.isLt))=
      ProverCommitWideBytes48.sourceCell q hq i := by
  dsimp only [source,byte]
  refine Fin.addCases (m := 16) (n := 16) (fun pos => ?_) (fun pos => ?_) i
  · obtain ⟨⟨l,j⟩,rfl⟩ := (finProdFinEquiv : (Fin 4 × Fin 4) ≃ Fin 16).surjective pos
    rw [show ProverCommitWideBytes48.sourceCell q hq (Fin.castAdd 16 (finProdFinEquiv (l,j)))=
      UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 l) j) from
        PV_RunJoin_WidePoint43.model_low q hq l j]
    have off : (Fin.castAdd 16 (finProdFinEquiv (l,j))).val=4*(Fin.castAdd 4 l).val+j.val := by
      change j.val+4*l.val=4*l.val+j.val
      omega
    rw [off,PV_RunJoin_WidePoint43.read,PV_RunJoin_WidePoint43.low_word]
    exact congrArg UInt8.ofFin (PV_RunJoin_WordLimb43.limb q.1 hq.1 l j)
  · obtain ⟨⟨l,j⟩,rfl⟩ := (finProdFinEquiv : (Fin 4 × Fin 4) ≃ Fin 16).surjective pos
    rw [show ProverCommitWideBytes48.sourceCell q hq (Fin.natAdd 16 (finProdFinEquiv (l,j)))=
      UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 l) j) from
        PV_RunJoin_WidePoint43.model_high q hq l j]
    have off : (Fin.natAdd 16 (finProdFinEquiv (l,j))).val=4*(Fin.natAdd 4 l).val+j.val := by
      change 16+(j.val+4*l.val)=4*(4+l.val)+j.val
      omega
    rw [off,PV_RunJoin_WidePoint43.read,PV_RunJoin_WidePoint43.high_word]
    exact congrArg UInt8.ofFin (PV_RunJoin_WordLimb43.limb q.2 hq.2 l j)

theorem image (q : Raw) (hq : canonical q) :
    (PV_RunJoin_FlatBytes35.wire (source q)).val.map byte=
      List.ofFn (ProverCommitWideBytes48.sourceCell q hq) := by
  apply List.ext_getElem
  · rw [List.length_map,(PV_RunJoin_FlatBytes35.wire _).property,List.length_ofFn]
    rfl
  · intro i hi hj
    have bound : i<32 := by
      rw [List.length_map,(PV_RunJoin_FlatBytes35.wire _).property] at hi
      exact hi
    simp only [List.getElem_map,List.getElem_ofFn]
    exact point q hq ⟨i,bound⟩
#print axioms point
#print axioms image
end R1Z.PV_RunJoin_WideImage43
