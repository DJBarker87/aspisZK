import PCM_Carriers
import PCM_Rejection
set_option autoImplicit false
namespace PCM_POOL_165
open RSL PCM
abbrev Args := Digest × UInt32 × UInt32 × Digest
/-- Frozen format.rs:225-232 forwards all four arguments unchanged to
spend::note_commitment (POOL:273). The installed model must be the complete
CLOSED callee model, including its same hash invocation's outcome, state and
ordered effects (PCI_Note.forwarding), never just a successful Digest value.
The input domain is precisely that callee's own (bf)(2) domain. -/
def RowSpec (domain : Args → Prop) (model : Args → State → Env → Observation Digest)
    (impl : Args → State → Env → Observation Digest) : Prop :=
  PCM.RowSpec domain (PCM.Graph domain model) impl

/-- Adding one fabricated log to an otherwise exact implementation is always
rejected, even when the real callee aborts; no success premise is used. -/
theorem rejects_extra_log (domain : Args → Prop)
    (model : Args → State → Env → Observation Digest) (a : Args) (ha : domain a) :
    ¬ RowSpec domain model (fun a s env =>
      { model a s env with events := .sdk (.log "fabricated") :: (model a s env).events }) := by
  apply PCM.graph_rejects domain model _ a PCM.state0 env0 ha
  intro he
  have hn := congrArg (fun o : Observation Digest => o.events.length) he
  simp only [List.length_cons] at hn
  exact Nat.succ_ne_self _ hn

#print axioms rejects_extra_log
end PCM_POOL_165
