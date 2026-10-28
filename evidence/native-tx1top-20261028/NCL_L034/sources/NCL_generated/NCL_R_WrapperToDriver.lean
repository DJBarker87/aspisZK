import NCL_R_DriverCuts
import RPz7_DrvC_AcceptedCalls
import RPz7_DrvC_NativeDecode
import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCL_WrapperToDriver
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_TrustedStd S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws
open DrvC_Installation
attribute [local irreducible] AdapterRw.r1_pool_adapter.owned.stage1_owned
  AspisR1CurrentCaller.verifier.candidate.tx1

/-- Exact first-wrapper premise shape of the headline, specialized to the
installed emitted owned body. No second transaction or independently supplied
public/semantic/checkpoint witness is needed for this TX1 inversion.
The actual Rust-to-wrapper association is NOT established by this theorem. -/
theorem source {F C A : Type} (c : Configuration F C)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A) (e : Entry)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (state final : A)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (accepted : first (AdapterRw.r1_pool_adapter.owned.stage1_owned (sdk c))
      copy allocator e program data state = ok (.Ok (saved,post,final))) :
    post = writeBracket e.heap 2 0 0 (S2W_CommittedCheckpoint.source (nativeBytes saved)) ∧
    ∃ proofAccount publicAccount pub raw statement semantic proof split,
      Slice.index_usize e.first 0#usize = ok proofAccount ∧
      Slice.index_usize e.first 1#usize = ok publicAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (sdk c) proofAccount = ok (.Ok raw) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (sdk c) publicAccount = ok (.Ok pub) ∧
      (sdk c).op47 pub = ok (.Ok statement) ∧
      (sdk c).op21 statement = ok (.Ok ()) ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        statement = ok semantic ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        raw {start:=688#usize,«end»:=58295#usize} = ok proof ∧
      raw.val.length = 58295 ∧ split = 10#usize ∧
      AspisR1CurrentCaller.verifier.candidate.tx1 (currentInstalled c) (currentDigest c)
        (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof split () none = ok (.Ok saved) := by
  obtain ⟨owned,write⟩ := first_accepted _ copy std allocator e program data state final saved post accepted
  obtain ⟨pa,pu,pub,raw,stmt,sem,proof,split,hpa,hpu,hraw,hpub,hd,hv,hs,range,child,len⟩ :=
    DrvC_NativeDecode.first_call_decoded (sdk c) program e.first data saved owned
  exact ⟨write,pa,pu,pub,raw,stmt,sem,proof,split,hpa,hpu,hraw,hpub,hd,hv,hs,range,len,
    DrvC_AcceptedCalls.split c sem pub proof split saved child,
    DrvC_AcceptedCalls.current_success c sem pub proof split saved child⟩
#print axioms source
end AspisR1.NCL_WrapperToDriver
end
