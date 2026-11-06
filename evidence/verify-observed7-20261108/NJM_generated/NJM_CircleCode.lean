import NJM_CircleJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_CircleCode
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)

/-- Closed concrete dictionary: only the installed circle operation is used. -/
def dispatch {H : Type} (D : aspis_core.Digest32 H)
 (t : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord) (row : U8) :
 Code (core.result.Result NJM_CircleJoin.Point r1_wire.Error × r1_wire.SemanticTranscript H) :=
 match row with
 | 25#uscalar => do
   let pair ← S1SemanticCode.sampleBlock D t 25#u8 record.framed
   NJM_CircleJoin.after .First pair
 | 26#uscalar => do
   let pair ← S1SemanticCode.sampleBlock D t 26#u8 record.framed
   NJM_CircleJoin.after .Second pair
 | _ => pure (.Err .InvalidRow,t)

def source {H : Type} (D : aspis_core.Digest32 H)
 (t : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord) :=
 dispatch D t record record.row

/-- The complete original Code execution with circle concretely installed.
B appears only in this internal dictionary-erasure lemma; it is absent from
source and every native root. All child abort prefixes remain in the bind. -/
theorem dispatch_eq {H : Type} (B : FinishModel.Boundaries) (D : aspis_core.Digest32 H)
 (t : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord) (row : U8) :
 run (NIX_ValidatedCut.dispatch (F3M_CircleSource.install B) D t record row)=
 run (dispatch D t record row) := by
 by_cases first : row=25#u8
 · subst row
   rw [NIX_DispatchRun.first]
   change _ = run (S1SemanticCode.sampleBlock D t 25#u8 record.framed >>= NJM_CircleJoin.after .First)
   rw [NGX_RunBind.bind_run]
   exact NJM_CircleJoin.append_continuation B .First _ _
 · by_cases second : row=26#u8
   · subst row
     rw [NIX_DispatchRun.second]
     change _ = run (S1SemanticCode.sampleBlock D t 26#u8 record.framed >>= NJM_CircleJoin.after .Second)
     rw [NGX_RunBind.bind_run]
     exact NJM_CircleJoin.append_continuation B .Second _ _
   · unfold NIX_ValidatedCut.dispatch dispatch
     split
     · change run (S1SemanticCode.sampleBlock D t 25#u8 record.framed >>= _) = run (S1SemanticCode.sampleBlock D t 25#u8 record.framed >>= _)
       rw [NGX_RunBind.bind_run,NGX_RunBind.bind_run]
       exact NJM_CircleJoin.append_continuation B .First _ _
     · change run (S1SemanticCode.sampleBlock D t 26#u8 record.framed >>= _) = run (S1SemanticCode.sampleBlock D t 26#u8 record.framed >>= _)
       rw [NGX_RunBind.bind_run,NGX_RunBind.bind_run]
       exact NJM_CircleJoin.append_continuation B .Second _ _
     · split <;> first | contradiction | rfl

theorem original {H : Type} (B : FinishModel.Boundaries) (D : aspis_core.Digest32 H)
 (t : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord) :
 run (S1SemanticCode.circleValidated (F3M_CircleSource.install B) D t record)=
 run (source D t record) := by
 rw [← NIX_ValidatedCut.source]
 change run (NIX_ValidatedCut.dispatch (F3M_CircleSource.install B) D t record record.row)=_
 exact dispatch_eq B D t record record.row

#print axioms dispatch_eq
#print axioms original
end AspisR1.NJM_CircleCode
end
