import R1Z.PV_RunJoin_ClaimImageList49
import R1Z.PV_RunJoin_ClaimValues49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimStreamImage49
open Aeneas Aeneas.Std ProverRwFull
open ProverRwDictionaryTower (fromW)
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode)
theorem complete (c : Nat → Nat → Old.Q) (x y : Old.Q) (z : Fin 29 → Old.Q)
    (hz : ∀ l,Canonical (z l))
    (hd : ∀ l,decode (z l)=ProverCommitEval47.messageEval
      (fun j : Fin 1024 => decode (c l.val (AspisR1.rowNat j.val))) (decode x) (decode y)) :
    (PV_RunJoin_ClaimImage48.bytes (List.ofFn (fun l : Fin 29 => fromW (ProverCommitNativeOps47.embedded (z l))))).map
      PV_RunJoin_WideImage43.byte=
      PV_RunJoin_ClaimImageList49.stream (fun l => List.ofFn (ProverCommitValueRange47.bytes
        (ProverCommitY1Bytes47.model (fun j => c l (AspisR1.rowNat j)) x y))) 0 29 := by
  let zs : Nat → Old.Q := fun l => if hl : l<29 then z ⟨l,hl⟩ else zero
  have ordered : PV_RunJoin_OrderedList48.run (fun l => fromW (ProverCommitNativeOps47.embedded (zs l))) 0 29=
      List.ofFn (fun l : Fin 29 => fromW (ProverCommitNativeOps47.embedded (z l))) := by
    rw [PV_RunJoin_OrderedList48.complete]
    simp only [Nat.zero_add,zs,dif_pos (Fin.isLt _)]
  rw [←ordered]
  apply PV_RunJoin_ClaimImageList49.complete
  · intro l hl
    have hzv : zs l=z ⟨l,hl⟩ := by simp only [zs,dif_pos hl]
    rw [hzv,PV_RunJoin_ClaimCellImage49.complete _ (hz ⟨l,hl⟩)]
    have eq : ProverCommitValueRange47.embed (decode (z ⟨l,hl⟩))=
        ProverCommitY1Bytes47.model (fun j => c l (AspisR1.rowNat j)) x y := by
      rw [hd ⟨l,hl⟩,ProverCommitY1Bytes47.model,ProverCommitEval47.message_embed]
    rw [eq]
  · omega
#print axioms complete
end R1Z.PV_RunJoin_ClaimStreamImage49
