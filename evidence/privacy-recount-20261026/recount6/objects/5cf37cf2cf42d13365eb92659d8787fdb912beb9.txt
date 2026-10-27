import R1Z.ProverCommitWordBytes47
import R1Z.ProverCommitNativeOps47
/-! Canonical source-limb byte image, before the native generator binding. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitLimbBytes47
open Aeneas Aeneas.Std Result ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.RetainedFieldByteCodec AspisR1.RetainedExactLimbCodec
open AspisR1.StrictWideByteCodec AspisR1.WideExactLimbCodec
open ProverCommitValueRange47 ProverCommitCompact43
open AspisR1.ExtractedCurrentQM31Exact

def limbs (q : Old.Q) (hq : Canonical q) : QM31Limbs :=
  ![⟨q.c0.a.val,hq.1.1⟩,⟨q.c0.b.val,hq.1.2⟩,⟨q.c1.a.val,hq.2.1⟩,⟨q.c1.b.val,hq.2.2⟩]

def sourceLimb (q : Old.Q) : Fin 4 → U32 := ![q.c0.a,q.c0.b,q.c1.a,q.c1.b]

theorem residue_cast (v : M31Value) : m31ResidueEquiv v=
    (v.val : AspisV8R15.ExactTowerBase.M31Exact) := by
  apply ZMod.val_injective AspisV8R15.ExactTowerBase.P
  change v.val=(v.val : ZMod AspisV8R15.ExactTowerBase.P).val
  rw [ZMod.val_natCast_of_lt v.isLt]

theorem limbs_decode (q : Old.Q) (hq : Canonical q) : qm31ExactLimbEquiv (limbs q hq)=decode q := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      simp [qm31ExactLimbEquiv,limbsToQM31Exact,residue_cast,limbs,decode]
  · apply QuadraticAlgebra.ext <;>
      simp [qm31ExactLimbEquiv,limbsToQM31Exact,residue_cast,limbs,decode]

theorem source_word (q : Old.Q) (hq : Canonical q) (i : Fin 4) :
    m31AsRawWord (limbs q hq i)=ProverCommitWordBytes47.rawWord (sourceLimb q i) := by
  fin_cases i <;> rfl

theorem limb_bytes (q : Old.Q) (hq : Canonical q) (i : Fin 4) :
    (core.num.U32.to_le_bytes (sourceLimb q i)).val.map ProverCommitWordBytes47.rawByte =
      List.ofFn (encodeM31LE (limbs q hq i)) := by
  rw [ProverCommitWordBytes47.word]
  unfold encodeM31LE
  rw [source_word]

def sourceCell (q : Old.Q) (hq : Canonical q) : Cell :=
  Fin.append (fun i : Fin 16 => UInt8.ofFin (encodeQM31LE (limbs q hq) i)) (fun _ : Fin 16 => 0)

theorem source_image (q : Old.Q) (hq : Canonical q) :
    sourceCell q hq=bytes (embed (decode q)) := by
  have hl : qm31ExactLimbEquiv.symm (decode q)=limbs q hq := by
    apply qm31ExactLimbEquiv.injective
    rw [Equiv.apply_symm_apply,limbs_decode]
  funext i
  refine Fin.addCases (m := 16) (n := 16) (fun j => ?_) (fun j => ?_) i
  · simp only [sourceCell,Fin.append_left,bytes,embedded_limbs,hl,encodeWideLE,Fin.append_left]
  · simp only [sourceCell,Fin.append_right,bytes,embedded_limbs,encodeWideLE,Fin.append_right,
      zero_limbs,zero_bytes]
    rfl

theorem source_decode (q : Old.Q) (hq : Canonical q) :
    AspisR1.FoldedLeafCodec.decodeWide ((List.ofFn (sourceCell q hq)).map UInt8.toFin)=
      some (embed (decode q)) := by
  rw [source_image]
  exact bytes_decode _

theorem source_compact (q : Old.Q) (hq : Canonical q) (out : ProverCommitPublish43.Bytes) :
    cell (sourceCell q hq) out=.ok (out++low (sourceCell q hq)) := by
  rw [source_image]
  exact range_compact _ (embed_range _) out

#print axioms residue_cast
#print axioms limbs_decode
#print axioms source_word
#print axioms limb_bytes
#print axioms source_image
#print axioms source_decode
#print axioms source_compact
end R1Z.ProverCommitLimbBytes47
