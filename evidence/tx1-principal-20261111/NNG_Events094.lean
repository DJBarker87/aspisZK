import NNG_InstalledCalls094
import NNG_Events087
import NNG_TypedEvents
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Events094
open Aeneas Aeneas.Std Result NMT_tx1
abbrev Digest := aspis_core.digest.Digest32 Unit
abbrev Observer := Option (verifier.Phase → Result Unit)
abbrev Scratch := Array aspis_core.field.wide_exact.WideExact 29#usize
abbrev PrepareArgs := Digest × aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public ×
 Slice U8 × Unit × Observer × Scratch
abbrev BatchArgs := Digest × Slice U8 × verifier.Prepared × Array U8 32#usize × Usize × Unit
abbrev CheckpointArgs := Digest × verifier.Prepared × verifier.Accumulator × Slice U8 × Slice U8 × Unit

def prepare (env : RSL.Env) (a : PrepareArgs) : List RSL.Event :=
 (NMT_CallTree.run (NNG_Tree087.tree (NNG_PrepareEmission087.calls env)
  (NNG_PrepareAdapter094.input a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2))).2.flatMap
  (NNG_Events087.events env)
def batch (env : RSL.Env) (a : BatchArgs) : List RSL.Event :=
 NNG_BatchCall094.events env a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1
def checkpoint (env : RSL.Env) (a : CheckpointArgs) : List RSL.Event :=
 NNG_CheckpointCall094.events env a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1
/-- The digest and hash values are retained in the typed source arguments;
all three effectful children are interpreted at their SAME arguments. -/
def events (env : RSL.Env) (event : NMT_CallTree.Event) : List RSL.Event :=
 NNG_TypedEvents.select "TX1:087/prepare" (prepare env) event ++
 NNG_TypedEvents.select "verifier.candidate.batch_merkle" (batch env) event ++
 NNG_TypedEvents.select "verifier.checkpoint" (checkpoint env) event

theorem prepare_call {Reply : Type} (env : RSL.Env) (a : PrepareArgs) (r : Result Reply) :
 events env (.call "TX1:087/prepare" a r)=prepare env a := by
 simp [events,NNG_TypedEvents.select]
#print axioms prepare_call
theorem batch_call {Reply : Type} (env : RSL.Env) (a : BatchArgs) (r : Result Reply) :
 events env (.call "verifier.candidate.batch_merkle" a r)=batch env a := by
 simp [events,NNG_TypedEvents.select]
#print axioms batch_call
theorem checkpoint_call {Reply : Type} (env : RSL.Env) (a : CheckpointArgs) (r : Result Reply) :
 events env (.call "verifier.checkpoint" a r)=checkpoint env a := by
 simp [events,NNG_TypedEvents.select]
#print axioms checkpoint_call
theorem silent {Args Reply : Type} (env : RSL.Env) (site : String) (a : Args) (r : Result Reply)
 (prepareSite : site≠"TX1:087/prepare") (batchSite : site≠"verifier.candidate.batch_merkle")
 (checkpointSite : site≠"verifier.checkpoint") : events env (.call site a r)=[] := by
 simp [events,NNG_TypedEvents.select,prepareSite,batchSite,checkpointSite]
#print axioms silent
end AspisR1.NNG_Events094
