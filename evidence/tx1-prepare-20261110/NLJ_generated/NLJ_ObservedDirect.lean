import NLJ_RunAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_ObservedDirect
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)
abbrev Out (H : Type) := NKQ_ObservedStages.Out H
def afterBegin (F : S1SemanticCode.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (p : r1_wire.Prefix)
 (t : r1_wire.SemanticTranscript H) (r : core.result.Result r1_wire.Challenges r1_wire.Error) : Code (Out H) :=
 match r with
 | .Err e => pure (.Err e)
 | .Ok c => do
   VerifyPrefix.mark none 1#u8
   F D pub p t c none

def afterPublic (F : S1SemanticCode.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (p : r1_wire.Prefix)
 (r : core.result.Result (r1_wire.SemanticTranscript H) r1_wire.Error) : Code (Out H) :=
 match r with
 | .Err e => pure (.Err e)
 | .Ok t => do
   let (reply,after) ← S1SemanticCode.begin D p t
   afterBegin F D pub p after reply

def afterParsed (F : S1SemanticCode.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H)
 (r : core.result.Result r1_wire.Prefix r1_wire.Error) : Code (Out H) :=
 match r with
 | .Err e => pure (.Err e)
 | .Ok p => do
   VerifyPrefix.mark none 0#u8
   let reply ← S1SemanticCode.publicTranscript D pub hash p.c1_root
   afterPublic F D pub p reply

def verify (F : S1SemanticCode.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H) : Code (Out H) := do
 let reply ← PrefixAdapter.parseAccepted bytes
 afterParsed F D pub hash reply

/-- Every pure Try/residual administrative step is evaluated; digest events
and all complete Result arms are preserved. No native assertion is made. -/
theorem source (F : S1SemanticCode.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H) :
 run (verify F D pub bytes hash) = run (S1SemanticCode.verify F D pub bytes hash none) := by
 unfold verify S1SemanticCode.verify
 change run (PreparedHashCode.bind (show Code _ from liftM (PrefixAdapter.parseAccepted bytes)) _) =
  run (PreparedHashCode.bind (show Code _ from liftM (PrefixAdapter.parseAccepted bytes)) _)
 apply NLJ_RunAlgebra.bind_congr
 intro reply
 cases reply with
 | Err e => rfl
 | Ok p =>
   change run (PreparedHashCode.bind (S1SemanticCode.publicTranscript D pub hash p.c1_root) _) =
    run (PreparedHashCode.bind (S1SemanticCode.publicTranscript D pub hash p.c1_root) _)
   apply NLJ_RunAlgebra.bind_congr
   intro publicReply
   cases publicReply with
   | Err e => rfl
   | Ok t =>
     change run (PreparedHashCode.bind (S1SemanticCode.begin D p t) _) =
      run (PreparedHashCode.bind (S1SemanticCode.begin D p t) _)
     apply NLJ_RunAlgebra.bind_congr
     intro beginPair
     rcases beginPair with ⟨beginReply,after⟩
     cases beginReply <;> rfl
#print axioms source
#print source
end AspisR1.NLJ_ObservedDirect
end
