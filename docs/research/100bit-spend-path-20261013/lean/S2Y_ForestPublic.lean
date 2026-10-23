import S2Y_OwnedChildren

/-! Full ASF8 public bytes, not the 320-byte ASQ8 request or payment216.
No full-forest codec theorem is installed; the missing theorem is named below. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2Y_ForestPublic
open Aeneas Aeneas.Std Result
open S2LeadInterface MultiproofConeCanonical
abbrev Statement := AdapterRw.Cuts.Statement
abbrev Public := AdapterRw.LeadInputs.Public
abbrev Observer := AdapterRw.LeadInputs.Observer

/-- EXACT MISSING S6 theorem on the owned operation carriers: reencoding any
accepted full-forest decode reproduces ALL original bytes. Success-conditioned
is sufficient because the actual owned TX2 already supplies encoder success.
Concrete decoder/encoder installation is independently required. This Prop is
not an axiom and no instance is claimed. It excludes hashing-only equality. -/
def FullForestAcceptedRoundtrip (ops : AdapterRw.Ops) : Prop :=
  ∀ (original : Slice U8) (statement : Statement) (encoded : Array U8 1880#usize),
    ops.op47 original = ok (.Ok statement) →
    ops.op22 statement = ok (.Ok encoded) → encoded.val = original.val

/-- The missing codec law applies to the SAME reconstructed statement only.
Reconstruction identity is an independent named source obligation. -/
theorem reconstructed_bytes (ops : AdapterRw.Ops)
    (fullForestAcceptedRoundtrip : FullForestAcceptedRoundtrip ops)
    (original : Slice U8) (decoded reconstructed : Statement)
    (encoded : Array U8 1880#usize)
    (decode : ops.op47 original = ok (.Ok decoded))
    (encode : ops.op22 reconstructed = ok (.Ok encoded))
    (reconstructedStatementIdentity : reconstructed = decoded) :
    bytesOf (Array.to_slice encoded).val = bytesOf original.val ∧
    (bytesOf original.val).length = 1880 := by
  have same : encoded.val = original.val :=
    fullForestAcceptedRoundtrip original decoded encoded decode
      (by simpa only [reconstructedStatementIdentity] using encode)
  constructor
  · exact congrArg bytesOf same
  · have len : encoded.val.length = 1880 := by simpa using encoded.property
    simpa only [bytesOf,List.length_map] using (same ▸ len)

/-- Public-site retention uses byte equality of the actual two public arguments;
no equality of the proof arguments is needed for this one field. -/
theorem retained_public (ops : AdapterRw.Ops) (c : Inputs Observer)
    (childInputRetention : AdapterRw.LeadInputs.ChildInputRetention ops c)
    (p : Public) (pub1 proof1 pub2 proof2 checkpoint : Slice U8)
    (split : Usize) (out : alloc.vec.Vec U8)
    (first : AdapterRw.first_decoded ops p pub1 proof1 split = ok (.Ok out))
    (second : ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      pub2 proof2 checkpoint () none = ok (.Ok ()))
    (samePublicBytes : bytesOf pub2.val = bytesOf pub1.val) :
    ∀ s, c.reached s → bytesOf (c.publicInput s).val = bytesOf pub1.val := by
  intro s reached
  by_cases early : s.rank ≤ 3
  · rw [(childInputRetention.first p pub1 proof1 split out first s reached early).2.1]
  · rw [(childInputRetention.second pub2 proof2 checkpoint second s reached (by omega)).2.1]
    exact samePublicBytes

/-- Actual owned TX1 decoding and TX2 reconstruction/encoder/tx2 invocation.
The proof/public buffers and both child successes are DERIVED from the outer
accepted calls. The forest codec and child retention remain named hypotheses;
the reconstructed statement's identity remains a precise conditional result.
This does not construct S2CallerFacts or native observation reification. -/
theorem owned_public_field (ops : AdapterRw.Ops) (c : Inputs Observer)
    (fullForestAcceptedRoundtrip : FullForestAcceptedRoundtrip ops)
    (childInputRetention : AdapterRw.LeadInputs.ChildInputRetention ops c)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts1 accounts2 : Slice AdapterRw.Cuts.Account) (data1 data2 : Slice U8)
    (checkpoint1 : alloc.vec.Vec U8) (slot : core.result.Result U64 AdapterRw.Cuts.PE)
    (accepted1 : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts1 data1 =
      ok (.Ok checkpoint1))
    (accepted2 : AdapterRw.r1_pool_adapter.owned.stage2_owned ops program accounts2 data2 slot =
      ok (.Ok ())) :
    ∃ publicAccount pub statement semantic proof1 split validated encoded proof2 checkpoint2,
      Slice.index_usize accounts1 1#usize = ok publicAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops publicAccount = ok (.Ok pub) ∧
      ops.op47 pub = ok (.Ok statement) ∧
      AdapterRw.first_decoded ops semantic pub proof1 split = ok (.Ok checkpoint1) ∧
      AdapterRw.r1_pool_adapter.owned.validate_asq8 ops program accounts2 data2 slot =
        ok (.Ok validated) ∧
      ops.op22 validated.statement = ok (.Ok encoded) ∧
      ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        (Array.to_slice encoded) proof2 checkpoint2 () none = ok (.Ok ()) ∧
      (validated.statement = statement →
        bytesOf (Array.to_slice encoded).val = bytesOf pub.val ∧
        (bytesOf pub.val).length = 1880 ∧
        (∀ s, c.reached s → bytesOf (c.publicInput s).val = bytesOf pub.val)) := by
  obtain ⟨_,pu,pub,_,stmt,semantic,proof1,split,_,hpu,_,hpub,hd,first,_,_⟩ :=
    AdapterRw.Accepted.first_proof_shapes ops program accounts1 data1 checkpoint1 accepted1
  obtain ⟨v,_,_,_,ck,enc,proof2,_,_,hv,_,_,_,_,he,_,second,_,_⟩ :=
    AdapterRw.Cuts.stage2_call ops program accounts2 data2 slot accepted2
  refine ⟨pu,pub,stmt,semantic,proof1,split,v,enc,proof2,ck,hpu,hpub,hd,first,hv,he,second,?_⟩
  intro reconstructedStatementIdentity
  have same := reconstructed_bytes ops fullForestAcceptedRoundtrip pub stmt v.statement enc
    hd he reconstructedStatementIdentity
  exact ⟨same.1,same.2,retained_public ops c childInputRetention semantic pub proof1
    (Array.to_slice enc) proof2 ck split checkpoint1 first second same.1⟩

#print axioms reconstructed_bytes
#print axioms retained_public
#print axioms owned_public_field
end AspisR1.S2Y_ForestPublic
end
