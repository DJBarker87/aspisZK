import R1Z.PV_RunJoin_FlatBytes35
import R1Z.PV_RunJoin_FieldData34
import R1Z.ProverCommitWideBytes48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WideImage43
open Aeneas Aeneas.Std ProverRwFull
open ProverCommitPrimitive47 ProverCommitSubfieldOps47 ProverCommitWideOps48
open AspisR1.RetainedFieldByteCodec
abbrev W := aspis_core.field.wide_exact.WideExact

def source (q : Raw) : W := ⟨PV_RunJoin_FieldData34.source q.1,PV_RunJoin_FieldData34.source q.2⟩
def byte (b : U8) : UInt8 := UInt8.ofFin (ProverCommitWordBytes47.rawByte b)

theorem limb (q : Old.Q) (hq : Canonical q) (i j : Fin 4) :
    ProverCommitWordBytes47.rawByte (PV_RunJoin_FlatBytes35.byte
      (ProverCommitLimbBytes47.sourceLimb q i) j)=
      encodeM31LE (ProverCommitLimbBytes47.limbs q hq i) j := by
  have h := ProverCommitLimbBytes47.limb_bytes q hq i
  have hi : j.val<(core.num.U32.to_le_bytes (ProverCommitLimbBytes47.sourceLimb q i)).val.length := by
    rw [(core.num.U32.to_le_bytes _).property]
    exact j.isLt
  have hh := congrArg (fun xs : List Byte => xs[j.val]?) h
  simp only [List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,
    List.getElem?_ofFn,show j.val<4 from j.isLt,↓reduceDIte] at hh
  exact Option.some.inj hh

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
    interval_cases i
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.1 ⟨0,by decide⟩) ⟨0,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 ⟨0,by decide⟩) ⟨0,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.1 hq.1 ⟨0,by decide⟩ ⟨0,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.1 ⟨0,by decide⟩) ⟨1,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 ⟨0,by decide⟩) ⟨1,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.1 hq.1 ⟨0,by decide⟩ ⟨1,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.1 ⟨0,by decide⟩) ⟨2,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 ⟨0,by decide⟩) ⟨2,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.1 hq.1 ⟨0,by decide⟩ ⟨2,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.1 ⟨0,by decide⟩) ⟨3,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 ⟨0,by decide⟩) ⟨3,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.1 hq.1 ⟨0,by decide⟩ ⟨3,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.1 ⟨1,by decide⟩) ⟨0,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 ⟨1,by decide⟩) ⟨0,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.1 hq.1 ⟨1,by decide⟩ ⟨0,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.1 ⟨1,by decide⟩) ⟨1,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 ⟨1,by decide⟩) ⟨1,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.1 hq.1 ⟨1,by decide⟩ ⟨1,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.1 ⟨1,by decide⟩) ⟨2,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 ⟨1,by decide⟩) ⟨2,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.1 hq.1 ⟨1,by decide⟩ ⟨2,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.1 ⟨1,by decide⟩) ⟨3,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 ⟨1,by decide⟩) ⟨3,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.1 hq.1 ⟨1,by decide⟩ ⟨3,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.1 ⟨2,by decide⟩) ⟨0,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 ⟨2,by decide⟩) ⟨0,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.1 hq.1 ⟨2,by decide⟩ ⟨0,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.1 ⟨2,by decide⟩) ⟨1,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 ⟨2,by decide⟩) ⟨1,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.1 hq.1 ⟨2,by decide⟩ ⟨1,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.1 ⟨2,by decide⟩) ⟨2,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 ⟨2,by decide⟩) ⟨2,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.1 hq.1 ⟨2,by decide⟩ ⟨2,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.1 ⟨2,by decide⟩) ⟨3,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 ⟨2,by decide⟩) ⟨3,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.1 hq.1 ⟨2,by decide⟩ ⟨3,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.1 ⟨3,by decide⟩) ⟨0,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 ⟨3,by decide⟩) ⟨0,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.1 hq.1 ⟨3,by decide⟩ ⟨0,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.1 ⟨3,by decide⟩) ⟨1,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 ⟨3,by decide⟩) ⟨1,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.1 hq.1 ⟨3,by decide⟩ ⟨1,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.1 ⟨3,by decide⟩) ⟨2,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 ⟨3,by decide⟩) ⟨2,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.1 hq.1 ⟨3,by decide⟩ ⟨2,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.1 ⟨3,by decide⟩) ⟨3,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 ⟨3,by decide⟩) ⟨3,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.1 hq.1 ⟨3,by decide⟩ ⟨3,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.2 ⟨0,by decide⟩) ⟨0,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 ⟨0,by decide⟩) ⟨0,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.2 hq.2 ⟨0,by decide⟩ ⟨0,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.2 ⟨0,by decide⟩) ⟨1,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 ⟨0,by decide⟩) ⟨1,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.2 hq.2 ⟨0,by decide⟩ ⟨1,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.2 ⟨0,by decide⟩) ⟨2,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 ⟨0,by decide⟩) ⟨2,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.2 hq.2 ⟨0,by decide⟩ ⟨2,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.2 ⟨0,by decide⟩) ⟨3,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 ⟨0,by decide⟩) ⟨3,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.2 hq.2 ⟨0,by decide⟩ ⟨3,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.2 ⟨1,by decide⟩) ⟨0,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 ⟨1,by decide⟩) ⟨0,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.2 hq.2 ⟨1,by decide⟩ ⟨0,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.2 ⟨1,by decide⟩) ⟨1,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 ⟨1,by decide⟩) ⟨1,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.2 hq.2 ⟨1,by decide⟩ ⟨1,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.2 ⟨1,by decide⟩) ⟨2,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 ⟨1,by decide⟩) ⟨2,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.2 hq.2 ⟨1,by decide⟩ ⟨2,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.2 ⟨1,by decide⟩) ⟨3,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 ⟨1,by decide⟩) ⟨3,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.2 hq.2 ⟨1,by decide⟩ ⟨3,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.2 ⟨2,by decide⟩) ⟨0,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 ⟨2,by decide⟩) ⟨0,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.2 hq.2 ⟨2,by decide⟩ ⟨0,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.2 ⟨2,by decide⟩) ⟨1,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 ⟨2,by decide⟩) ⟨1,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.2 hq.2 ⟨2,by decide⟩ ⟨1,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.2 ⟨2,by decide⟩) ⟨2,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 ⟨2,by decide⟩) ⟨2,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.2 hq.2 ⟨2,by decide⟩ ⟨2,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.2 ⟨2,by decide⟩) ⟨3,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 ⟨2,by decide⟩) ⟨3,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.2 hq.2 ⟨2,by decide⟩ ⟨3,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.2 ⟨3,by decide⟩) ⟨0,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 ⟨3,by decide⟩) ⟨0,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.2 hq.2 ⟨3,by decide⟩ ⟨0,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.2 ⟨3,by decide⟩) ⟨1,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 ⟨3,by decide⟩) ⟨1,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.2 hq.2 ⟨3,by decide⟩ ⟨1,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.2 ⟨3,by decide⟩) ⟨2,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 ⟨3,by decide⟩) ⟨2,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.2 hq.2 ⟨3,by decide⟩ ⟨2,by decide⟩)
    · change UInt8.ofFin (ProverCommitWordBytes47.rawByte
        (PV_RunJoin_FlatBytes35.byte (ProverCommitLimbBytes47.sourceLimb q.2 ⟨3,by decide⟩) ⟨3,by decide⟩)) =
        UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 ⟨3,by decide⟩) ⟨3,by decide⟩)
      exact congrArg UInt8.ofFin (limb q.2 hq.2 ⟨3,by decide⟩ ⟨3,by decide⟩)
#print axioms limb
#print axioms image
end R1Z.PV_RunJoin_WideImage43
