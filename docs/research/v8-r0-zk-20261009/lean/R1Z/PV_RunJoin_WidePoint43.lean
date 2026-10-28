import R1Z.PV_RunJoin_WordLimb43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WidePoint43
open Aeneas Aeneas.Std ProverRwFull
open ProverCommitPrimitive47 ProverCommitSubfieldOps47 ProverCommitWideOps48
open AspisR1.RetainedFieldByteCodec
abbrev W := aspis_core.field.wide_exact.WideExact

def source (q : Raw) : W := ⟨PV_RunJoin_FieldData34.source q.1,PV_RunJoin_FieldData34.source q.2⟩
def byte (b : U8) : UInt8 := UInt8.ofFin (ProverCommitWordBytes47.rawByte b)
def word (x : W) : Fin 8 → U32 :=
  ![x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]

theorem read (x : W) (i : Fin 8) (j : Fin 4) :
    (PV_RunJoin_FlatBytes35.wire x).val[4*i.val+j.val]'(by
      rw [(PV_RunJoin_FlatBytes35.wire x).property]
      have := i.isLt;have := j.isLt;omega)=PV_RunJoin_FlatBytes35.byte (word x i) j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem low_word (q : Raw) (i : Fin 4) :
    word (source q) (Fin.castAdd 4 i)=ProverCommitLimbBytes47.sourceLimb q.1 i := by
  fin_cases i
  · change (PV_RunJoin_FieldData34.old (PV_RunJoin_FieldData34.source q.1)).c0.a=q.1.c0.a
    rw [PV_RunJoin_FieldData34.old_source]
  · change (PV_RunJoin_FieldData34.old (PV_RunJoin_FieldData34.source q.1)).c0.b=q.1.c0.b
    rw [PV_RunJoin_FieldData34.old_source]
  · change (PV_RunJoin_FieldData34.old (PV_RunJoin_FieldData34.source q.1)).c1.a=q.1.c1.a
    rw [PV_RunJoin_FieldData34.old_source]
  · change (PV_RunJoin_FieldData34.old (PV_RunJoin_FieldData34.source q.1)).c1.b=q.1.c1.b
    rw [PV_RunJoin_FieldData34.old_source]

theorem high_word (q : Raw) (i : Fin 4) :
    word (source q) (Fin.natAdd 4 i)=ProverCommitLimbBytes47.sourceLimb q.2 i := by
  fin_cases i
  · change (PV_RunJoin_FieldData34.old (PV_RunJoin_FieldData34.source q.2)).c0.a=q.2.c0.a
    rw [PV_RunJoin_FieldData34.old_source]
  · change (PV_RunJoin_FieldData34.old (PV_RunJoin_FieldData34.source q.2)).c0.b=q.2.c0.b
    rw [PV_RunJoin_FieldData34.old_source]
  · change (PV_RunJoin_FieldData34.old (PV_RunJoin_FieldData34.source q.2)).c1.a=q.2.c1.a
    rw [PV_RunJoin_FieldData34.old_source]
  · change (PV_RunJoin_FieldData34.old (PV_RunJoin_FieldData34.source q.2)).c1.b=q.2.c1.b
    rw [PV_RunJoin_FieldData34.old_source]

theorem model_low (q : Raw) (hq : canonical q) (i j : Fin 4) :
    ProverCommitWideBytes48.sourceCell q hq (Fin.castAdd 16 (limbByteIndex i j))=
      UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.1 hq.1 i) j) := by
  simp only [ProverCommitWideBytes48.sourceCell,Fin.append_left,encodeQM31LE,limbByteIndex,
    Equiv.symm_apply_apply]

theorem model_high (q : Raw) (hq : canonical q) (i j : Fin 4) :
    ProverCommitWideBytes48.sourceCell q hq (Fin.natAdd 16 (limbByteIndex i j))=
      UInt8.ofFin (encodeM31LE (ProverCommitLimbBytes47.limbs q.2 hq.2 i) j) := by
  simp only [ProverCommitWideBytes48.sourceCell,Fin.append_right,encodeQM31LE,limbByteIndex,
    Equiv.symm_apply_apply]
#print axioms read
#print axioms low_word
#print axioms high_word
#print axioms model_low
#print axioms model_high
end R1Z.PV_RunJoin_WidePoint43
