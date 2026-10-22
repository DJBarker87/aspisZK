import R1Z.ProverCommitWideOps48
import R1Z.ProverCommitLimbBytes47
/-! Canonical full-width source limb order and exact 32-byte image. The
native serializer binding is a separate full-width Kani gate. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitWideBytes48
open Aeneas Aeneas.Std Result ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitWideOps48
open AspisR1.RetainedFieldByteCodec AspisR1.RetainedExactLimbCodec
open AspisR1.StrictWideByteCodec AspisR1.WideExactLimbCodec

def sourceCell (x : Raw) (hx : canonical x) : Fin 32 → UInt8 :=
  Fin.append
    (fun i : Fin 16 => UInt8.ofFin (encodeQM31LE (ProverCommitLimbBytes47.limbs x.1 hx.1) i))
    (fun i : Fin 16 => UInt8.ofFin (encodeQM31LE (ProverCommitLimbBytes47.limbs x.2 hx.2) i))

theorem limbs_image (x : Raw) (hx : canonical x) :
    pairExactEquiv.symm (value x)=
      (ProverCommitLimbBytes47.limbs x.1 hx.1,ProverCommitLimbBytes47.limbs x.2 hx.2) := by
  apply pairExactEquiv.injective
  rw [Equiv.apply_symm_apply,pairExactEquiv_apply]
  simp only [pairToExact,ProverCommitLimbBytes47.limbs_decode,value]

theorem source_image (x : Raw) (hx : canonical x) :
    sourceCell x hx=ProverCommitValueRange47.bytes (value x) := by
  funext i
  refine Fin.addCases (m := 16) (n := 16) (fun j => ?_) (fun j => ?_) i
  · simp only [sourceCell,Fin.append_left,ProverCommitValueRange47.bytes,
      limbs_image x hx,encodeWideLE,Fin.append_left]
  · simp only [sourceCell,Fin.append_right,ProverCommitValueRange47.bytes,
      limbs_image x hx,encodeWideLE,Fin.append_right]

theorem source_decode (x : Raw) (hx : canonical x) :
    AspisR1.FoldedLeafCodec.decodeWide ((List.ofFn (sourceCell x hx)).map UInt8.toFin)=
      some (value x) := by
  rw [source_image]
  exact ProverCommitValueRange47.bytes_decode _

#print axioms limbs_image
#print axioms source_image
#print axioms source_decode
end R1Z.ProverCommitWideBytes48
