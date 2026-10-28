import R1Z.PV_RunJoin_FlatBytes35
import R1Z.PV_RunJoin_FieldData34
import R1Z.ProverCommitWideBytes48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WordLimb43
open Aeneas Aeneas.Std ProverRwFull
open ProverCommitPrimitive47 ProverCommitSubfieldOps47 ProverCommitWideOps48
open AspisR1.RetainedFieldByteCodec
abbrev W := aspis_core.field.wide_exact.WideExact

theorem limb (q : Old.Q) (hq : Canonical q) (i j : Fin 4) :
    ProverCommitWordBytes47.rawByte (PV_RunJoin_FlatBytes35.byte
      (ProverCommitLimbBytes47.sourceLimb q i) j)=
      encodeM31LE (ProverCommitLimbBytes47.limbs q hq i) j := by
  have h := ProverCommitLimbBytes47.limb_bytes q hq i
  have hi : j.val<(core.num.U32.to_le_bytes (ProverCommitLimbBytes47.sourceLimb q i)).val.length := by
    rw [(core.num.U32.to_le_bytes _).property]
    exact j.isLt
  have hh := congrArg (fun xs : List AspisR1.RetainedFieldByteCodec.Byte => xs[j.val]?) h
  simp only [List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,
    List.getElem?_ofFn,show j.val<4 from j.isLt,↓reduceDIte] at hh
  exact Option.some.inj hh

#print axioms limb
end R1Z.PV_RunJoin_WordLimb43
