import S2E_SuccessInversion
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2E
open S2E_Reference.S2E_Reference

/-- Fixed original reference inputs. The mutable child state includes whatever
oracle/allocator/event interpretation is eventually instantiated; it is not reset
between child calls. This is not yet a relation to native or SBF memory. -/
structure Original (S : Type) where
  state : S
  sdk : SDK
  program : Array U8 32#usize
  data : Slice U8

def E {C S : Type} (ops : S2E_Reference.Ops) (children : Children C S)
    (original : Original S) : Result (CallerResult S) :=
  stage1 ops children original.state original.sdk original.program original.data

/-- Success inversion of the extracted enclosing reference, on fixed originals.
Every successor is obtained from the preceding actual call, not supplied as an
independent successful execution. Native acceptance → this equality is OPEN. -/
theorem execution_prefix {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (original : Original S) (finalState : S) (finalSdk : SDK)
    (accepted : E ops children original = ok (.Ok (),finalState,finalSdk)) :
    ∃ account acquired guards continued,
      shape1 ops original.data (alloc.vec.Vec.len original.sdk.accounts) = ok (.Ok ()) ∧
      admission ops original.program original.sdk = ok (.Ok ()) ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
        original.sdk.accounts 2#usize = ok account ∧
      owned_acquire_checkpoint original.sdk
        {checkpoint:=none,«public»:=none,proof:=none} account.data_slot =
        ok (.Ok (),acquired,guards) ∧
      checkpoint_continuation ops children original.state acquired original.data =
        ok (.Ok (),finalState,continued) ∧
      owned_release_guards continued guards = ok finalSdk := by
  unfold E stage1 at accepted
  obtain ⟨reply,shape,rest⟩ := bind_success
    (shape1 ops original.data (alloc.vec.Vec.len original.sdk.accounts)) _ _ accepted
  cases reply with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at rest
    cases rest
  | Ok unit =>
    cases unit
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at rest
    obtain ⟨reply,admitted,rest⟩ := bind_success
      (admission ops original.program original.sdk) _ _ rest
    cases reply with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at rest
      cases rest
    | Ok unit =>
      cases unit
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at rest
      obtain ⟨account,read,rest⟩ := bind_success
        (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
          original.sdk.accounts 2#usize) _ _ rest
      obtain ⟨⟨reply,acquired,guards⟩,borrowed,rest⟩ := bind_success
        (owned_acquire_checkpoint original.sdk
          {checkpoint:=none,«public»:=none,proof:=none} account.data_slot) _ _ rest
      cases reply with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at rest
        cases rest
      | Ok unit =>
        cases unit
        obtain ⟨⟨result,state1,continued⟩,ran,rest⟩ := bind_success
          (checkpoint_continuation ops children original.state acquired original.data) _ _ rest
        obtain ⟨released,release,rest⟩ := bind_success (owned_release_guards continued guards) _ _ rest
        cases rest
        exact ⟨account,acquired,guards,continued,shape,admitted,read,borrowed,ran,release⟩

/-- The scan and next continuation refer to the checkpoint acquired by E. -/
theorem checkpoint_success {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (state finalState : S) (sdk finalSdk : SDK) (data : Slice U8)
    (accepted : checkpoint_continuation ops children state sdk data =
      ok (.Ok (),finalState,finalSdk)) :
    ∃ account cell,
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
        sdk.accounts 2#usize = ok account ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
        sdk.data_cells account.data_slot = ok cell ∧
      nonzero_from (alloc.vec.Vec.deref cell.bytes) (alloc.vec.Vec.len cell.bytes) = ok false ∧
      public_continuation ops children state sdk data = ok (.Ok (),finalState,finalSdk) := by
  unfold checkpoint_continuation at accepted
  obtain ⟨account,readAccount,rest⟩ := bind_success
    (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount) sdk.accounts 2#usize) _ _ accepted
  obtain ⟨cell,readCell,rest⟩ := bind_success
    (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell) sdk.data_cells account.data_slot) _ _ rest
  obtain ⟨hit,scanned,rest⟩ := bind_success
    (nonzero_from (alloc.vec.Vec.deref cell.bytes) (alloc.vec.Vec.len cell.bytes)) _ _ rest
  cases hit with
  | true => cases rest
  | false => exact ⟨account,cell,readAccount,readCell,scanned,rest⟩

/-- Public bytes are those cloned from the precise acquired public cell.
An original-byte frame and allocator erasure are still required for native use. -/
theorem public_success {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (state finalState : S) (sdk finalSdk : SDK) (data : Slice U8)
    (accepted : public_continuation ops children state sdk data =
      ok (.Ok (),finalState,finalSdk)) :
    ∃ account acquired cell publicBytes beforeRelease,
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
        sdk.accounts 1#usize = ok account ∧
      owned_acquire_shared sdk account.data_slot = ok (.Ok (),acquired) ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
        acquired.data_cells account.data_slot = ok cell ∧
      alloc.vec.CloneVec.clone core.clone.CloneU8 cell.bytes = ok publicBytes ∧
      decoded_continuation ops children state acquired (alloc.vec.Vec.deref publicBytes) data =
        ok (.Ok (),finalState,beforeRelease) ∧
      release_shared beforeRelease account.data_slot = ok finalSdk := by
  unfold public_continuation at accepted
  obtain ⟨account,readAccount,rest⟩ := bind_success
    (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount) sdk.accounts 1#usize) _ _ accepted
  obtain ⟨⟨reply,acquired⟩,borrowed,rest⟩ := bind_success (owned_acquire_shared sdk account.data_slot) _ _ rest
  cases reply with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at rest
    cases rest
  | Ok unit =>
    cases unit
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at rest
    obtain ⟨cell,readCell,rest⟩ := bind_success
      (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell) acquired.data_cells account.data_slot) _ _ rest
    obtain ⟨publicBytes,cloned,rest⟩ := bind_success (alloc.vec.CloneVec.clone core.clone.CloneU8 cell.bytes) _ _ rest
    obtain ⟨⟨result,state1,beforeRelease⟩,ran,rest⟩ := bind_success
      (decoded_continuation ops children state acquired (alloc.vec.Vec.deref publicBytes) data) _ _ rest
    obtain ⟨released,release,rest⟩ := bind_success (release_shared beforeRelease account.data_slot) _ _ rest
    cases rest
    exact ⟨account,acquired,cell,publicBytes,beforeRelease,readAccount,borrowed,readCell,cloned,ran,release⟩

/-- Gate, split byte, first child and proof release are a contiguous reference
continuation. The returned proof vector is the clone actually used in that run. -/
theorem proof_success {C S : Type} (ops : S2E_Reference.Ops)
    (children : Children C S) (state finalState : S) (sdk finalSdk : SDK)
    (statement : Statement) (publicInput data : Slice U8) (candidate : Array U8 688#usize)
    (accepted : proof_continuation ops children state sdk statement publicInput data candidate =
      ok (.Ok (),finalState,finalSdk)) :
    ∃ proofAccount cpAccount acquired cell proofBytes splitByte split beforeRelease,
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
        sdk.accounts 0#usize = ok proofAccount ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount)
        sdk.accounts 2#usize = ok cpAccount ∧
      owned_acquire_shared sdk proofAccount.data_slot = ok (.Ok (),acquired) ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
        acquired.data_cells proofAccount.data_slot = ok cell ∧
      alloc.vec.CloneVec.clone core.clone.CloneU8 cell.bytes = ok proofBytes ∧
      proof_gate ops (alloc.vec.Vec.deref proofBytes) candidate = ok (.Ok ()) ∧
      Slice.index_usize data 1#usize = ok splitByte ∧
      lift (UScalar.cast .Usize splitByte) = ok split ∧
      first_and_copy children state acquired statement publicInput (alloc.vec.Vec.deref proofBytes)
        split cpAccount.data_slot = ok (.Ok (),finalState,beforeRelease) ∧
      release_shared beforeRelease proofAccount.data_slot = ok finalSdk := by
  unfold proof_continuation at accepted
  obtain ⟨pa,readProof,rest⟩ := bind_success
    (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount) sdk.accounts 0#usize) _ _ accepted
  obtain ⟨ca,readCP,rest⟩ := bind_success
    (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedAccount) sdk.accounts 2#usize) _ _ rest
  obtain ⟨⟨reply,acquired⟩,borrowed,rest⟩ := bind_success (owned_acquire_shared sdk pa.data_slot) _ _ rest
  cases reply with
  | Err error =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at rest
    cases rest
  | Ok unit =>
    cases unit
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at rest
    obtain ⟨cell,readCell,rest⟩ := bind_success
      (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell) acquired.data_cells pa.data_slot) _ _ rest
    obtain ⟨proofBytes,cloned,rest⟩ := bind_success (alloc.vec.CloneVec.clone core.clone.CloneU8 cell.bytes) _ _ rest
    obtain ⟨reply,gated,rest⟩ := bind_success (proof_gate ops (alloc.vec.Vec.deref proofBytes) candidate) _ _ rest
    cases reply with
    | Err error =>
      simp only [bind_tc_ok] at rest
      obtain ⟨released,release,rest⟩ := bind_success (release_shared acquired pa.data_slot) _ _ rest
      cases rest
    | Ok unit =>
      cases unit
      let body : Result (S × SDK × core.result.Result Unit PE) := do
        let byte ← Slice.index_usize data 1#usize
        let split ← lift (UScalar.cast .Usize byte)
        let (result,state1,sdk1) ← first_and_copy children state acquired statement publicInput
          (alloc.vec.Vec.deref proofBytes) split ca.data_slot
        ok (state1,sdk1,result)
      change (do
        let (state1,sdk1,result) ← body
        let sdk2 ← release_shared sdk1 pa.data_slot
        ok (result,state1,sdk2)) = ok (.Ok (),finalState,finalSdk) at rest
      obtain ⟨⟨state1,beforeRelease,result⟩,ranBody,rest⟩ := bind_success body _ _ rest
      obtain ⟨released,release,rest⟩ := bind_success (release_shared beforeRelease pa.data_slot) _ _ rest
      cases rest
      unfold body at ranBody
      obtain ⟨splitByte,readSplit,rest⟩ := bind_success (Slice.index_usize data 1#usize) _ _ ranBody
      obtain ⟨split,castSplit,rest⟩ := bind_success (lift (UScalar.cast .Usize splitByte)) _ _ rest
      obtain ⟨⟨result,state2,sdk2⟩,ran,rest⟩ := bind_success
        (first_and_copy children state acquired statement publicInput (alloc.vec.Vec.deref proofBytes) split ca.data_slot) _ _ rest
      cases rest
      exact ⟨pa,ca,acquired,cell,proofBytes,splitByte,split,beforeRelease,
        readProof,readCP,borrowed,readCell,cloned,gated,readSplit,castSplit,ran,release⟩

#print axioms proof_success

#print axioms E
#print axioms execution_prefix
#print axioms checkpoint_success
#print axioms public_success
end AspisR1.S2E
