import S2Y_ChildGeometry

/-! Exact child-input ports on accepted OWNED caller arguments. The checked
internal ranges and the cross-transaction identity are NOT installed here. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2Y_OwnedChildren
open Aeneas Aeneas.Std Result
open S2LeadInterface MultiproofConeCanonical OraclePortCompactDraft

/-- OPEN internal source range observation, not a physical-view conclusion. -/
def PhysicalRange (proof actual : Slice U8) (slot : Nat) : Prop :=
  ∃ start finish : Usize,
    start.val = OraclePortSelectedDraft.slotStart slot ∧
    finish.val = start.val + 32*OraclePortSelectedDraft.capacity slot ∧
    finish.val ≤ proof.val.length ∧
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start := start, «end» := finish} = ok actual

def NodeRanges (proof : Slice U8) (nodes : Nat → Nat → Slice U8) (batch : Nat) : Prop :=
  ∀ k, k < 3 → PhysicalRange proof (nodes batch k) (3*batch+k)

/-- OPEN observation at canonical_scan's check_values call, on stored compact
bytes. This is distinct from wide_view.y1, which holds expanded 928 bytes. -/
def Y1Range (proof actual : Slice U8) : Prop :=
  7495 ≤ proof.val.length ∧
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    proof {start := 7031#usize, «end» := 7495#usize} = ok actual

theorem batch_views (proof : Slice U8) (nodes : Nat → Nat → Slice U8)
    (batch : Nat) (tr : RawCutTranscriptRun.ErasedPrefix) (parsed : Parsed)
    (parser : OraclePortStoredParserC4.parseReached (bytesOf proof.val) tr = some parsed)
    (ranges : NodeRanges proof nodes batch) :
    ∀ k, k < 3 → bytesOf (nodes batch k).val =
      slice parsed.wire (OraclePortSelectedDraft.slotStart (3*batch+k))
        (32*OraclePortSelectedDraft.capacity (3*batch+k)) := by
  intro k bound
  obtain ⟨start,finish,offset,width,within,run⟩ := ranges k bound
  exact S2Y_ChildGeometry.physical_slot proof (nodes batch k) tr parsed parser
    (3*batch+k) start finish offset width within run

/-- Exact lead nodeViews field. Both actual children must supply ranges, and
TX2 must retain the same stored bytes. No semantic-row/physical-slot equation. -/
theorem node_views {Observer : Type} (c : Inputs Observer) (proof1 proof2 : Slice U8)
    (tr : RawCutTranscriptRun.ErasedPrefix) (parsed : Parsed)
    (parser : OraclePortStoredParserC4.parseReached (bytesOf proof1.val) tr = some parsed)
    (sameStoredProof : bytesOf proof2.val = bytesOf proof1.val)
    (firstChildNodeRanges : NodeRanges proof1 c.nodes 0)
    (secondChildNodeRanges : NodeRanges proof2 c.nodes 1) :
    ∀ b k, b < 2 → k < 3 → bytesOf (c.nodes b k).val =
      slice parsed.wire (OraclePortSelectedDraft.slotStart (3*b+k))
        (32*OraclePortSelectedDraft.capacity (3*b+k)) := by
  have parser2 : OraclePortStoredParserC4.parseReached (bytesOf proof2.val) tr = some parsed := by
    rw [sameStoredProof]; exact parser
  intro b k hb hk
  have cases : b = 0 ∨ b = 1 := by omega
  rcases cases with h | h
  · subst b; exact batch_views proof1 c.nodes 0 tr parsed parser firstChildNodeRanges k hk
  · subst b; exact batch_views proof2 c.nodes 1 tr parsed parser2 secondChildNodeRanges k hk

/-- Exact lead y1Input field and the S8 scan result. The observation equation
links the lead's tx1 proof snapshot to the actual outer child's argument. -/
theorem y1_input {Observer : Type} (c : Inputs Observer) (proof : Slice U8)
    (tr : RawCutTranscriptRun.ErasedPrefix) (parsed : Parsed)
    (parser : OraclePortStoredParserC4.parseReached (bytesOf proof.val) tr = some parsed)
    (firstChildY1Range : Y1Range proof c.y1)
    (tx1ProofObservation : c.reached .tx1 → c.proof .tx1 = proof) :
    (c.reached .tx1 → c.y1 = S8JoinFrozenScan.segment (c.proof .tx1) 7031 464) ∧
    S8OwnedP6.check_values_owned c.y1 = ok (.Ok ()) := by
  have scan := S2Y_ChildGeometry.y1_scan proof c.y1 tr parsed parser
    firstChildY1Range.1 firstChildY1Range.2
  exact ⟨fun reached => by rw [tx1ProofObservation reached]; exact scan.1,scan.2⟩

/-- Depth-first TX1 port: derive the actual account reads, decoder and child
invocation from whole owned acceptance, then expose the precise remaining
internal-cut hypotheses ON THESE arguments. No child success premise. -/
theorem owned_first {Observer : Type} (c : Inputs Observer) (ops : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice AdapterRw.Cuts.Account)
    (data : Slice U8) (checkpoint : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data =
      ok (.Ok checkpoint)) :
    ∃ pa pu pub raw statement semantic proof split,
      Slice.index_usize accounts 0#usize = ok pa ∧
      Slice.index_usize accounts 1#usize = ok pu ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops pa = ok (.Ok raw) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops pu = ok (.Ok pub) ∧
      ops.op47 pub = ok (.Ok statement) ∧
      AdapterRw.first_decoded ops semantic pub proof split = ok (.Ok checkpoint) ∧
      proof.val.length = 57607 ∧
      (∀ tr parsed, OraclePortStoredParserC4.parseReached (bytesOf proof.val) tr = some parsed →
        NodeRanges proof c.nodes 0 → Y1Range proof c.y1 →
        (c.reached .tx1 → c.proof .tx1 = proof) →
        (∀ k, k < 3 → bytesOf (c.nodes 0 k).val =
          slice parsed.wire (OraclePortSelectedDraft.slotStart k)
            (32*OraclePortSelectedDraft.capacity k)) ∧
        (c.reached .tx1 → c.y1 = S8JoinFrozenScan.segment (c.proof .tx1) 7031 464) ∧
        S8OwnedP6.check_values_owned c.y1 = ok (.Ok ())) := by
  obtain ⟨pa,pu,pub,raw,stmt,semantic,proof,split,hpa,hpu,hr,hpub,hd,first,len,_⟩ :=
    AdapterRw.Accepted.first_proof_shapes ops program accounts data checkpoint accepted
  refine ⟨pa,pu,pub,raw,stmt,semantic,proof,split,hpa,hpu,hr,hpub,hd,first,len,?_⟩
  intro tr parsed parser nodes y1 observed
  have batch := batch_views proof c.nodes 0 tr parsed parser nodes
  have scan := y1_input c proof tr parsed parser y1 observed
  exact ⟨by simpa only [Nat.mul_zero,Nat.zero_add] using batch,scan⟩

/-- Actual TX2 argument port, including the SAME reconstructed statement's
encoder. Conditional batch1 geometry uses this invocation's selected proof. -/
theorem owned_second {Observer : Type} (c : Inputs Observer) (ops : AdapterRw.Ops)
    (program : AdapterRw.solana_pubkey.Pubkey) (accounts : Slice AdapterRw.Cuts.Account)
    (data : Slice U8) (slot : core.result.Result U64 AdapterRw.Cuts.PE)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage2_owned ops program accounts data slot =
      ok (.Ok ())) :
    ∃ validated proofAccount checkpointAccount raw checkpoint publicArray proof start finish,
      AdapterRw.r1_pool_adapter.owned.validate_asq8 ops program accounts data slot = ok (.Ok validated) ∧
      Slice.index_usize accounts 0#usize = ok proofAccount ∧
      Slice.index_usize accounts 6#usize = ok checkpointAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops proofAccount = ok (.Ok raw) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops checkpointAccount = ok (.Ok checkpoint) ∧
      ops.op22 validated.statement = ok (.Ok publicArray) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        raw {start := start, «end» := finish} = ok proof ∧
      ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        (Array.to_slice publicArray) proof checkpoint () none = ok (.Ok ()) ∧
      (∀ tr parsed, OraclePortStoredParserC4.parseReached (bytesOf proof.val) tr = some parsed →
        NodeRanges proof c.nodes 1 → ∀ k, k < 3 → bytesOf (c.nodes 1 k).val =
          slice parsed.wire (OraclePortSelectedDraft.slotStart (3+k))
            (32*OraclePortSelectedDraft.capacity (3+k))) := by
  obtain ⟨v,pa,ca,raw,ck,pub,proof,start,finish,hv,hpa,hca,hr,hck,enc,range,second,_,_⟩ :=
    AdapterRw.Cuts.stage2_call ops program accounts data slot accepted
  refine ⟨v,pa,ca,raw,ck,pub,proof,start,finish,hv,hpa,hca,hr,hck,enc,range,second,?_⟩
  intro tr parsed parser nodes
  exact batch_views proof c.nodes 1 tr parsed parser nodes

#print axioms batch_views
#print axioms node_views
#print axioms y1_input
#print axioms owned_first
#print axioms owned_second
end AspisR1.S2Y_OwnedChildren
end
