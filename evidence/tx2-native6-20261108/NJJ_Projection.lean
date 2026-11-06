import NJJ_QueryOps
import NJC_FilledClause
set_option autoImplicit false
noncomputable section
namespace NJJ_Projection
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- Exactly the fields that the frozen TX2 common body reads. This auxiliary
relation is for proving irrelevance, not a dictionary parameter at a positive
root. Unused TX1/authentication fields are absent on purpose. -/
def reads (a b : VTop_Stages.Ops) : Prop :=
 @a.op0=@b.op0 ∧ a.op2=b.op2 ∧ @a.op5=@b.op5 ∧ a.op6=b.op6 ∧
 a.op9=b.op9 ∧ a.op10=b.op10 ∧ a.op11=b.op11 ∧ a.op13=b.op13 ∧
 a.op14=b.op14 ∧ a.op15=b.op15 ∧ a.op16=b.op16 ∧ @a.op17=@b.op17 ∧
 @a.op18=@b.op18 ∧ a.op19=b.op19 ∧ a.op20=b.op20 ∧ a.op21=b.op21 ∧
 a.op22=b.op22 ∧ a.op23=b.op23 ∧ a.unwrap32=b.unwrap32

/-- The complete source Result cannot depend on uncalled dictionary fields.
This is a body-congruence fact only, not native security closure. -/
theorem source (a b : VTop_Stages.Ops) (same : reads a b) {H : Type}
 (d : VTop_Stages.aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H) :
 NHT_EmittedCommon.tx2_common a d pub proof ck hash none=
 NHT_EmittedCommon.tx2_common b d pub proof ck hash none := by
 rcases same with ⟨h0,h2,h5,h6,h9,h10,h11,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,hu⟩
 unfold NHT_EmittedCommon.tx2_common
 simp only [h0,h2,h5,h6,h9,h10,h11,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,hu]

#print axioms source
end NJJ_Projection
