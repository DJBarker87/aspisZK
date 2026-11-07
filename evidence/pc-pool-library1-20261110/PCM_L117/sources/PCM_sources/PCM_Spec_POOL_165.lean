import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_165
open RSL PCM
abbrev Args := Digest × UInt32 × UInt32 × Digest
/-- The sole call is spend::note_commitment, POOL:273 (PCI_Note.forwarding).
The typed field is the graph of that deterministic CLOSED callee, not an
arbitrary successful invocation relation. Native wrapper association stays OPEN. -/
def RowSpec (domain : Args → Prop) (note : Args → Digest) (impl : Args → Env → Obs Digest) : Prop :=
  ∀ a, domain a → ∀ env, impl a env = ⟨.ret (note a),[]⟩

theorem rejects_const_abort (domain : Args → Prop) (note : Args → Digest) (a : Args) (ha : domain a) :
    ¬ RowSpec domain note (fun _ _ => ⟨.abort,[]⟩) := by
  intro h
  have he := h a ha env0
  cases he
#print axioms rejects_const_abort
end PCM_POOL_165
