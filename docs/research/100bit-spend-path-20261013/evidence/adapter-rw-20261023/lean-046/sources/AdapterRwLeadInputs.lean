import AdapterRwAccepted
import S2LeadInterface

/-! Actual lead field types. The missing whole-child site-provenance contracts
are named hypotheses, never inferred from a pure value instance or extraction.
No S2CallerFacts instance, native trace or same-input cross-transaction law is
fabricated here. -/
set_option autoImplicit false
namespace AspisR1.AdapterRw.LeadInputs
open Aeneas Aeneas.Std Result
open S2LeadInterface MultiproofConeCanonical
abbrev Observer := AdapterRw.aspis_r1_cost_probe.verifier.Phase → Result Unit
abbrev Public := AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public

/-- OPEN whole-child input provenance. The current S2G pure-value contract does
not instantiate these laws. They are weaker than full source/effect refinement
and contain no byte equality between independently supplied transactions. -/
structure ChildInputRetention (ops : AdapterRw.Ops) (c : Inputs Observer) : Prop where
  first : ∀ (p : Public) (pub proof : Slice U8) (split : Usize) (out : alloc.vec.Vec U8),
    AdapterRw.first_decoded ops p pub proof split = ok (.Ok out) →
    ∀ s, c.reached s → s.rank ≤ 3 →
      c.proof s = proof ∧ c.publicInput s = pub ∧ c.observer s = none
  second : ∀ (pub proof checkpoint : Slice U8),
    ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      pub proof checkpoint () none = ok (.Ok ()) →
    ∀ s, c.reached s → 3 < s.rank →
      c.proof s = proof ∧ c.publicInput s = pub ∧ c.observer s = none

/-- Three exact Required14 field types from matching successful child calls.
Matching proof/public arguments MUST be established at the native cuts; neither
readonly flags nor this theorem prove inter-transaction equality. -/
theorem input_fields (ops : AdapterRw.Ops) (c : Inputs Observer)
    (children : ChildInputRetention ops c) (p : Public) (pub proof checkpoint : Slice U8)
    (split : Usize) (out : alloc.vec.Vec U8)
    (first : AdapterRw.first_decoded ops p pub proof split = ok (.Ok out))
    (second : ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      pub proof checkpoint () none = ok (.Ok ())) :
    (∀ s, c.reached s → bytesOf (c.proof s).val = bytesOf proof.val) ∧
    (∀ s, c.reached s → bytesOf (c.publicInput s).val = bytesOf pub.val) ∧
    (∀ s, c.reached s → c.observer s = none) := by
  have sites : ∀ s, c.reached s →
      c.proof s = proof ∧ c.publicInput s = pub ∧ c.observer s = none := by
    intro s reached
    by_cases early : s.rank ≤ 3
    · exact children.first p pub proof split out first s reached early
    · exact children.second pub proof checkpoint second s reached (by omega)
  exact ⟨fun s reached => congrArg (fun v : Slice U8 => bytesOf v.val) (sites s reached).1,
    fun s reached => congrArg (fun v : Slice U8 => bytesOf v.val) (sites s reached).2.1,
    fun s reached => (sites s reached).2.2⟩

/-- Native TX1 call-site proofLength and prefix/suffix bytes in the lead's
Byte carrier. The selected bytes are tied to the actual verifier invocation. -/
theorem first_byte_fields (ops : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice Cuts.Account)
    (data : Slice U8) (checkpoint : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data =
      ok (.Ok checkpoint)) :
    ∃ proofAccount publicAccount publicInput raw statement semantic selected split,
      Slice.index_usize accounts 0#usize = ok proofAccount ∧
      Slice.index_usize accounts 1#usize = ok publicAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops proofAccount = ok (.Ok raw) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops publicAccount = ok (.Ok publicInput) ∧
      ops.op47 publicInput = ok (.Ok statement) ∧
      AdapterRw.first_decoded ops semantic publicInput selected split = ok (.Ok checkpoint) ∧
      (bytesOf selected.val).length = 57607 ∧
      bytesOf raw.val = (bytesOf raw.val).take 688 ++ bytesOf selected.val := by
  obtain ⟨pa,pu,pub,raw,stmt,semantic,selected,split,hpa,hpu,hr,hpub,hd,first,len,suffix⟩ :=
    Accepted.first_proof_shapes ops program accounts data checkpoint accepted
  refine ⟨pa,pu,pub,raw,stmt,semantic,selected,split,hpa,hpu,hr,hpub,hd,first,?_,?_⟩
  · simpa only [bytesOf,List.length_map] using len
  · have same := congrArg bytesOf suffix
    simpa only [bytesOf,List.map_append,List.map_take] using same

#print axioms input_fields
#print axioms first_byte_fields
end AspisR1.AdapterRw.LeadInputs
