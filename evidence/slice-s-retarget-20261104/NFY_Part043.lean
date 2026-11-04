import Lean
import NFY_Part041
import NFY_Part042
import ExtractedAdapterReconstructSuccess
import NFY_Part020
import Aeneas
import NFY_Part035
import RPz7_Op3I_Nonvacuity
import NFY_Part024
import RPz7_S6NativeAfterstateCodecV1
import AdapterRwModel
import AdapterRwScalar
import RPz7_S6CurrentAdapterCarrierV1
import CurrentCompactCallerModelV1
import CurrentClaimSumModel
import RPz7_NP6_ClaimsModel
import CheckpointBytes4Ops
import Port4A_ReaderInstall
import AspisR1PublicPreparation.Funs

-- BEGIN copied JHf_RequestDomain: lean/JHf_RequestDomain.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHf_RequestDomain
open Aeneas Aeneas.Std Result

def value : Array U8 32#usize := match NFY_JHd_RequestCarrier.actual.«public» with
  | .PrivateTransfer p=>p.deployment_domain
  | .Withdrawal p=>p.deployment_domain

theorem same_public : value=NFY_JFt_SnapshotValue.value.deployment_domain := rfl
#print axioms same_public

theorem mismatch : NFY_JHf_DomainBytes.master≠value := by
  rw [same_public]
  exact NFY_JHf_DomainBytes.mismatch
#print axioms mismatch

theorem compare : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    value NFY_JHf_DomainBytes.master=ok true := rfl
#print axioms compare
end AspisR1.NFY_JHf_RequestDomain
-- END copied JHf_RequestDomain
-- BEGIN copied JHf_NoReconstruction: lean/JHf_NoReconstruction.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHf_NoReconstruction
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct r1_pool_adapter
open aspis_statement.pool_v1.pair_forest_terminal

def request := JHf_Carrier.toRequest NFY_JHd_RequestCarrier.actual

theorem source (a : AuthenticatedAsq8Accounts)
    (candidate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (faithful : a.live_snapshot.deployment_domain=NFY_JHf_DomainBytes.master) :
    ¬∃ out,reconstruct_asq8_statement request a candidate=ok (.Ok out) := by
  rintro ⟨out,run⟩
  obtain ⟨_,_,same,valid⟩:=AdapterReconstructSuccess.reconstruct_success request a candidate out run
  have guard:=NFY_JHf_RawStatementDomainGuard.source out valid
  rw [same] at guard
  change core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    NFY_JHf_RequestDomain.value a.live_snapshot.deployment_domain=ok false at guard
  rw [faithful,NFY_JHf_RequestDomain.compare] at guard
  cases guard
#print axioms source
end AspisR1.NFY_JHf_NoReconstruction
-- END copied JHf_NoReconstruction
-- BEGIN copied JHf_ReconstructionSlot: lean/JHf_ReconstructionSlot.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHf_ReconstructionSlot
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

def source (request : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1)
    (accounts : r1_pool_adapter.AuthenticatedAsq8Accounts)
    (candidate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) :
    Result (core.result.Result
      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
      solana_program_error.ProgramError) := do
  let result ← AspisR1AdapterReconstruct.r1_pool_adapter.reconstruct_asq8_statement
    (JHf_Carrier.toRequest request) (JHf_Carrier.toAuthenticatedAsq8Accounts accounts)
    (JHf_Carrier.toPoolV1PairVerifiedAfterstateV1 candidate)
  match result with
  | .Ok statement=>ok (.Ok (JHf_Carrier.fromPoolV1PairForestTerminalStatementV1 statement))
  | .Err error=>ok (.Err (NFY_JHf_ProgramErrorCarrier.fromRaw error))

theorem no_success (accounts : r1_pool_adapter.AuthenticatedAsq8Accounts)
    (candidate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (faithful : accounts.live_snapshot.deployment_domain=NFY_JHf_DomainBytes.master) :
    ¬∃ out,source NFY_JHd_RequestCarrier.actual accounts candidate=ok (.Ok out) := by
  rintro ⟨out,run⟩
  unfold source at run
  have impossible:=NFY_JHf_NoReconstruction.source (JHf_Carrier.toAuthenticatedAsq8Accounts accounts)
    (JHf_Carrier.toPoolV1PairVerifiedAfterstateV1 candidate) faithful
  change ¬∃ out,AspisR1AdapterReconstruct.r1_pool_adapter.reconstruct_asq8_statement
    (JHf_Carrier.toRequest NFY_JHd_RequestCarrier.actual) (JHf_Carrier.toAuthenticatedAsq8Accounts accounts)
    (JHf_Carrier.toPoolV1PairVerifiedAfterstateV1 candidate)=ok (.Ok out) at impossible
  cases call : AspisR1AdapterReconstruct.r1_pool_adapter.reconstruct_asq8_statement
      (JHf_Carrier.toRequest NFY_JHd_RequestCarrier.actual) (JHf_Carrier.toAuthenticatedAsq8Accounts accounts)
      (JHf_Carrier.toPoolV1PairVerifiedAfterstateV1 candidate) with
  | fail e=>simp only [call,bind_tc_fail] at run;cases run
  | div=>simp only [call,bind_tc_div] at run;cases run
  | ok result=>
    cases result with
    | Err e=>simp only [call,bind_tc_ok] at run;cases run
    | Ok value=>exact impossible ⟨value,call⟩
#print axioms no_success
end AspisR1.NFY_JHf_ReconstructionSlot
-- END copied JHf_ReconstructionSlot
-- BEGIN copied JGx_ProofAccount: lean/JGx_ProofAccount.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JGx_ProofAccount
open Aeneas Aeneas.Std Result

theorem proof_length : NFY_JFx_NativeBytes.proof.val.length=57607 := NFY_JFx_NativeBytes.proofBytes_length
#print axioms proof_length
attribute [local irreducible] NFY_JFx_NativeBytes.proof

def value (headerBytes : Array U8 688#usize) : Slice U8 :=
  ⟨headerBytes.val++NFY_JFx_NativeBytes.proof.val,by
    rw [List.length_append,headerBytes.property,proof_length]
    scalar_tac⟩

theorem length (headerBytes : Array U8 688#usize) : (value headerBytes).length=58295 := by
  change (headerBytes.val++NFY_JFx_NativeBytes.proof.val).length=58295
  rw [List.length_append,headerBytes.property,proof_length]
  rfl
#print axioms length

theorem suffix (headerBytes : Array U8 688#usize) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      (value headerBytes) {start:=688#usize,«end»:=58295#usize}=ok NFY_JFx_NativeBytes.proof := by
  obtain ⟨out,run,contents,size⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      (⟨688#usize,58295#usize⟩ : core.ops.range.Range Usize) (value headerBytes)
      (by decide) (by rw [length];decide))
  have same : out=NFY_JFx_NativeBytes.proof := by
    apply Subtype.ext
    rw [contents]
    change ((headerBytes.val++NFY_JFx_NativeBytes.proof.val).drop 688).take 57607=_
    have hlen : headerBytes.val.length=688 := headerBytes.property
    have dropped : (headerBytes.val++NFY_JFx_NativeBytes.proof.val).drop 688=NFY_JFx_NativeBytes.proof.val := by
      have h : (headerBytes.val++NFY_JFx_NativeBytes.proof.val).drop headerBytes.val.length=NFY_JFx_NativeBytes.proof.val := List.drop_left
      simpa only [hlen] using h
    rw [dropped,List.take_of_length_le (by rw [proof_length])]

  exact run.trans (congrArg ok same)
#print axioms suffix
end AspisR1.NFY_JGx_ProofAccount
end
-- END copied JGx_ProofAccount
-- BEGIN copied JHb_Header: lean/JHb_Header.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JHb_Header
open Aeneas Aeneas.Std Result
/-- Exact candidate header retained in the physical public, not an independent
selected successful encoder return. -/
def value : Array U8 688#usize :=
  ⟨NFY_JFu_PublicRange.afterstate.val,NFY_JFu_PublicRange.length 976 688 (by decide)⟩
attribute [local irreducible] NFY_JFu_PublicRange.afterstate
def account : Slice U8 := NFY_JGx_ProofAccount.value value

theorem candidate : AspisR1TerminalDecoder.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1
    value.to_slice = ok (.Ok NFY_JFt_AfterstateValue.value) := by
  have same : value.to_slice = NFY_JFu_PublicRange.afterstate := by
    apply Subtype.ext
    rfl
  rw [same]
  exact NFY_JFs_AfterstateDecode.source
#print axioms candidate

theorem suffix : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    account {start:=688#usize,«end»:=58295#usize}=ok NFY_JFx_NativeBytes.proof :=
  NFY_JGx_ProofAccount.suffix value
#print axioms suffix

theorem length : account.length=58295 := NFY_JGx_ProofAccount.length value
#print axioms length
end AspisR1.NFY_JHb_Header
end
-- END copied JHb_Header
-- BEGIN copied JFx_NativeHeader: lean/JFx_NativeHeader.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JFx_NativeHeader
open Aeneas Aeneas.Std Result
open NFY_JFx_NativeBytes

theorem first_sixteen : proof.val.take 16 =
    [82#u8,49#u8,80#u8,51#u8,67#u8,66#u8,49#u8,56#u8,2#u8,
      0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8] := by
  change proofBytes.take 16 = _
  simp only [proofBytes,List.take_append,List.length_append,
    NFY_JFx_DataProof00.length,
    NFY_JFx_DataProof01.length,
    NFY_JFx_DataProof02.length,
    NFY_JFx_DataProof03.length,
    NFY_JFx_DataProof04.length,
    NFY_JFx_DataProof05.length,
    NFY_JFx_DataProof06.length,
    NFY_JFx_DataProof07.length,
    NFY_JFx_DataProof08.length,
    NFY_JFx_DataProof09.length,
    NFY_JFx_DataProof10.length,
    NFY_JFx_DataProof11.length,
    NFY_JFx_DataProof12.length,
    NFY_JFx_DataProof13.length,
    NFY_JFx_DataProof14.length,
    Nat.reduceAdd,Nat.reduceSub,List.take_zero,List.append_nil]
  simp only [NFY_JFx_DataProof00.bytes,List.take_append,List.length_append,
    NFY_JFx_DataProof00.c00_length,NFY_JFx_DataProof00.c01_length,
    NFY_JFx_DataProof00.c02_length,NFY_JFx_DataProof00.c03_length,
    NFY_JFx_DataProof00.c04_length,NFY_JFx_DataProof00.c05_length,
    NFY_JFx_DataProof00.c06_length,NFY_JFx_DataProof00.c07_length,
    NFY_JFx_DataProof00.c08_length,NFY_JFx_DataProof00.c09_length,
    NFY_JFx_DataProof00.c10_length,NFY_JFx_DataProof00.c11_length,
    NFY_JFx_DataProof00.c12_length,NFY_JFx_DataProof00.c13_length,
    NFY_JFx_DataProof00.c14_length,NFY_JFx_DataProof00.c15_length,
    NFY_JFx_DataProof00.c16_length,NFY_JFx_DataProof00.c17_length,
    NFY_JFx_DataProof00.c18_length,NFY_JFx_DataProof00.c19_length,
    NFY_JFx_DataProof00.c20_length,NFY_JFx_DataProof00.c21_length,
    NFY_JFx_DataProof00.c22_length,NFY_JFx_DataProof00.c23_length,
    NFY_JFx_DataProof00.c24_length,NFY_JFx_DataProof00.c25_length,
    NFY_JFx_DataProof00.c26_length,NFY_JFx_DataProof00.c27_length,
    NFY_JFx_DataProof00.c28_length,NFY_JFx_DataProof00.c29_length,
    NFY_JFx_DataProof00.c30_length,NFY_JFx_DataProof00.c31_length,
    NFY_JFx_DataProof00.c32_length,NFY_JFx_DataProof00.c33_length,
    NFY_JFx_DataProof00.c34_length,NFY_JFx_DataProof00.c35_length,
    NFY_JFx_DataProof00.c36_length,NFY_JFx_DataProof00.c37_length,
    NFY_JFx_DataProof00.c38_length,NFY_JFx_DataProof00.c39_length,
    NFY_JFx_DataProof00.c40_length,NFY_JFx_DataProof00.c41_length,
    NFY_JFx_DataProof00.c42_length,NFY_JFx_DataProof00.c43_length,
    NFY_JFx_DataProof00.c44_length,NFY_JFx_DataProof00.c45_length,
    NFY_JFx_DataProof00.c46_length,NFY_JFx_DataProof00.c47_length,
    NFY_JFx_DataProof00.c48_length,NFY_JFx_DataProof00.c49_length,
    NFY_JFx_DataProof00.c50_length,NFY_JFx_DataProof00.c51_length,
    NFY_JFx_DataProof00.c52_length,NFY_JFx_DataProof00.c53_length,
    NFY_JFx_DataProof00.c54_length,NFY_JFx_DataProof00.c55_length,
    NFY_JFx_DataProof00.c56_length,NFY_JFx_DataProof00.c57_length,
    NFY_JFx_DataProof00.c58_length,NFY_JFx_DataProof00.c59_length,
    NFY_JFx_DataProof00.c60_length,NFY_JFx_DataProof00.c61_length,
    NFY_JFx_DataProof00.c62_length,NFY_JFx_DataProof00.c63_length,
    Nat.reduceAdd,Nat.reduceSub,List.take_zero,List.append_nil]
  rfl

#print axioms first_sixteen
end AspisR1.NFY_JFx_NativeHeader
end
-- END copied JFx_NativeHeader
-- BEGIN copied JHf_ProofWindow: lean/JHf_ProofWindow.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHf_ProofWindow
open Aeneas Aeneas.Std Result
attribute [local irreducible] NFY_JFx_NativeBytes.proof NFY_JHb_Header.value NFY_JHb_Header.account

theorem first : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JHb_Header.account {start:=0#usize,«end»:=688#usize}=ok NFY_JHb_Header.value.to_slice := by
  obtain ⟨out,run,contents,size⟩:=WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      (⟨0#usize,688#usize⟩ : core.ops.range.Range Usize) NFY_JHb_Header.account
      (by decide) (by rw [NFY_JHb_Header.length];decide))
  have same : out=NFY_JHb_Header.value.to_slice := by
    apply Subtype.ext
    rw [contents]
    simp only [List.slice,NFY_JHb_Header.account,NFY_JGx_ProofAccount.value,
      show (0#usize).val=0 from rfl,show (688#usize).val=688 from rfl,
      Nat.sub_zero,List.drop_zero,List.take_append,
      NFY_JHb_Header.value.property,Array.to_slice,Nat.sub_self,List.take_zero,List.append_nil,
      List.take_length]
    exact List.take_of_length_le (by rw [NFY_JHb_Header.value.property];exact Nat.le_refl 688)
  exact run.trans (congrArg ok same)
#print axioms first

theorem proof_tag : NFY_JFx_NativeBytes.proof.val[8]?=some 2#u8 := by
  have h:=congrArg (fun xs : List U8=>xs[8]?) NFY_JFx_NativeHeader.first_sixteen
  rw [List.getElem?_take_of_lt (by decide : 8<16)] at h
  exact h
#print axioms proof_tag

theorem tag : Slice.index_usize NFY_JHb_Header.account 696#usize=ok 2#u8 := by
  apply NFY_JFt_Index.source _ _ (by rw [NFY_JHb_Header.length];decide) 2#u8
  simp only [NFY_JHb_Header.account,NFY_JGx_ProofAccount.value,List.getElem?_append,
    NFY_JHb_Header.value.property,show (696#usize).val=696 from rfl]
  exact proof_tag
#print axioms tag
end AspisR1.NFY_JHf_ProofWindow
-- END copied JHf_ProofWindow
-- BEGIN copied JHf_ScanCodec: lean/JHf_ScanCodec.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHf_ScanCodec
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_terminal
attribute [local irreducible] NFY_JHb_Header.value

theorem encoded : encode_pool_v1_pair_verified_afterstate_v1 NFY_JFt_AfterstateValue.value=
    ok (.Ok NFY_JHb_Header.value) := by
  obtain ⟨bytes,contents,call⟩:=AspisS6NativeAfterstateCodec.accepted_inverse
    NFY_JHb_Header.value.to_slice NFY_JFt_AfterstateValue.value NFY_JHb_Header.candidate
  have same : bytes=NFY_JHb_Header.value := Subtype.ext contents
  exact same ▸ call
#print axioms encoded
end AspisR1.NFY_JHf_ScanCodec
-- END copied JHf_ScanCodec
-- BEGIN copied JHd_ScanValue: lean/JHd_ScanValue.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHd_ScanValue
open Aeneas Aeneas.Std Result

def candidate : AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  ⟨NFY_JFt_AfterstateValue.value.next_pair_index,NFY_JFt_AfterstateValue.value.next_root,
    NFY_JFt_AfterstateValue.value.next_frontier⟩
def value : AdapterRw.r1_pool_adapter.ScannedAsqaProof := ⟨candidate,57607#usize⟩
theorem length : value.proof_length=57607#usize := rfl
#print axioms length
end AspisR1.NFY_JHd_ScanValue
-- END copied JHd_ScanValue
-- BEGIN copied JHf_Scan: lean/JHf_Scan.lean
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFY_JHf_Scan
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_terminal

/-- Direct source control-flow model of scan_proof_buffer. Both codecs are
actual extracted operations; no successful child return is installed.
Native/source/ELF association of this model remains a separate obligation. -/
def source (bytes : Slice U8) : Result (core.result.Result
    AdapterRw.r1_pool_adapter.ScannedAsqaProof AdapterRw.solana_program_error.ProgramError) := do
  let expected ← lift (Usize.checked_add 688#usize 57607#usize)
  match expected with
  | none=>ok (.Err .InvalidAccountData)
  | some size=>
    if Slice.len bytes != size then ok (.Err .InvalidAccountData) else do
      let header ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes {start:=0#usize,«end»:=688#usize}
      let decoded ← decode_pool_v1_pair_verified_afterstate_v1 header
      match decoded with
      | .Err _=>ok (.Err .InvalidAccountData)
      | .Ok candidate=>
        let encoded ← encode_pool_v1_pair_verified_afterstate_v1 candidate
        match encoded with
        | .Err _=>ok (.Err .InvalidAccountData)
        | .Ok encoded=>
          if encoded.val != header.val then ok (.Err .InvalidAccountData) else do
            let tag ← Slice.index_usize bytes 696#usize
            if tag != 2#u8 then ok (.Err .InvalidAccountData) else
              ok (.Ok ⟨AspisS6CurrentAdapterCarrier.fromPoolV1PairVerifiedAfterstateV1 candidate,57607#usize⟩)

attribute [local irreducible] NFY_JHb_Header.account NFY_JHb_Header.value

theorem real : source NFY_JHb_Header.account=ok (.Ok NFY_JHd_ScanValue.value) := by
  have size : Slice.len NFY_JHb_Header.account=58295#usize := by
    have h:=NFY_JHb_Header.length
    scalar_tac
  unfold source
  simp only [lift,show Usize.checked_add 688#usize 57607#usize=some 58295#usize from AdapterRw.Scalar.checked_add_eq _ _ _ (by scalar_tac),
    bind_tc_ok,size,show (58295#usize !=58295#usize)=false from rfl,Bool.false_eq_true,↓reduceIte,
    NFY_JHf_ProofWindow.first,NFY_JHb_Header.candidate,NFY_JHf_ScanCodec.encoded,
    show (NFY_JHb_Header.value.val !=NFY_JHb_Header.value.to_slice.val)=false from by simp only [Array.to_slice];simp,
    NFY_JHf_ProofWindow.tag,show (2#u8 !=2#u8)=false from rfl]
  rfl
#print axioms real
end AspisR1.NFY_JHf_Scan
end
-- END copied JHf_Scan
-- BEGIN copied NBC_ReleaseLeaves: lean/NBC_ReleaseLeaves.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBC_ReleaseLeaves
open Aeneas Aeneas.Std Result

/-- Every release caller obtains precisely None; no observer hypothesis. -/
theorem observer (ops : AdapterRw.Ops) : AdapterRw.observer ops = ok none := rfl

/-- Release mark has no callback and no effect, for every actual phase. -/
theorem mark (phase : AspisR1CurrentCaller.verifier.Phase) :
    AspisR1CurrentCaller.verifier.mark none phase = ok () := rfl

/-- The retained release trace definition ignores all of its arguments. -/
theorem value (tag : U16) (index : Usize)
    (x : AspisR1CurrentPreparedClaim.aspis_core.field.WideExact) :
    AspisR1CurrentPreparedClaim.trace.value tag index x = ok () := rfl

abbrev Parts := Slice (Slice U8)
abbrev Digest := Array U8 32#usize

/-- The exact emitted to_bytes body; the hash value is an arbitrary reply. -/
def toBytes (digest : Digest) : Result Digest := ok digest

/-- Frozen three-line source wrapper, with only the runtime hashv call external. -/
def sourceDigest (hashv : Parts → Result Digest) (_self : AdapterRw.SolanaDigest)
    (parts : Parts) : Result Digest := do
  let digest ← hashv parts
  toBytes digest

/-- All Result paths and the SAME ordered parts are preserved. -/
theorem digest_result (hashv : Parts → Result Digest)
    (self : AdapterRw.SolanaDigest) (parts : Parts) :
    sourceDigest hashv self parts = hashv parts := by
  cases h : hashv parts <;> simp only [sourceDigest, h, toBytes,
    bind_tc_ok, bind_tc_fail, bind_tc_div]

/-- Local dictionary installation only. This does not identify the adopted
headline dictionary with the concrete source wrapper. -/
def digestOps (ops : AdapterRw.Ops) (hashv : Parts → Result Digest) : AdapterRw.Ops :=
  {ops with op43 := sourceDigest hashv}

theorem digest_installed (ops : AdapterRw.Ops) (hashv : Parts → Result Digest)
    (self : AdapterRw.SolanaDigest) (parts : Parts) :
    (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (digestOps ops hashv)).digest self parts =
      hashv parts := digest_result hashv self parts

/-- Program error VALUE port only. The actual msg! runtime effect is retained
as an open native obligation; enum conversions in NBI2 are not this wrapper. -/
def errorValue (_e : AdapterRw.aspis_r1_cost_probe.verifier.Error) :
    Result AdapterRw.solana_program_error.ProgramError :=
  ok .InvalidInstructionData

def errorOps (ops : AdapterRw.Ops) : AdapterRw.Ops := {ops with op44 := errorValue}

theorem error_installed (ops : AdapterRw.Ops)
    (e : AdapterRw.aspis_r1_cost_probe.verifier.Error) :
    (errorOps ops).op44 e = ok .InvalidInstructionData := rfl

#print axioms observer
#print axioms mark
#print axioms value
#print axioms digest_result
#print axioms digest_installed
#print axioms error_installed
end NFY_NBC_ReleaseLeaves
-- END copied NBC_ReleaseLeaves
-- BEGIN copied NBC_Filled: lean/NBC_Filled.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBC_Filled
open Aeneas Aeneas.Std Result
open AspisR1 AspisR1ClaimsUnrolledParent AspisR1.NP6_StdModel

/-- Reuse the complete existing pure std value law, retaining allocation
failure and deriving contents rather than assuming successful filled output.
Native std/allocator/ownership association is expressly outside this theorem. -/
theorem result (reservation : Reservation) {T : Type}
    (copy : core.marker.Copy T) (n : Usize) (value : T)
    (cloned : copy.cloneInst.clone value = ok value) :
    aspis_core.r0.heap.filled (ClaimsUnrolledFinish.external (calls reservation)) copy n value =
      match reservation with
      | .Err _ => ok (.Err .Allocation)
      | .Ok () => ok (.Ok (⟨List.replicate n.val value, by simp; scalar_tac⟩ : alloc.vec.Vec T)) :=
  AspisR1.NP6_ClaimsModel.filled_contents reservation copy n value cloned

#print axioms result
end NFY_NBC_Filled
-- END copied NBC_Filled
-- BEGIN copied NBC_Audit: lean/NBC_Audit.lean
set_option autoImplicit false
#print axioms NFY_NBC_ReleaseLeaves.observer
#print axioms NFY_NBC_ReleaseLeaves.mark
#print axioms NFY_NBC_ReleaseLeaves.value
#print axioms NFY_NBC_ReleaseLeaves.digest_result
#print axioms NFY_NBC_ReleaseLeaves.digest_installed
#print axioms NFY_NBC_ReleaseLeaves.error_installed
#print axioms NFY_NBC_Filled.result
-- END copied NBC_Audit
-- BEGIN copied NBG_Transport: lean/NBG_Transport.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBG_Transport
open Aeneas Aeneas.Std Result
abbrev V := AspisR1PublicPreparation.transport.Variant
abbrev CV := AspisR1Stage2.transport.Variant

def port : V → CV
  | .S1 => .S1 | .S2 => .S2 | .D => .D

def folds : V → Usize
  | .S1 => 1#usize | .S2 => 2#usize | .D => 2#usize

theorem folds_result (v : V) :
    AspisR1PublicPreparation.transport.Variant.folds v = ok (folds v) := by
  cases v <;> simp [AspisR1PublicPreparation.transport.Variant.folds,
    AspisR1PublicPreparation.transport.Variant.Insts.CoreCmpPartialEqVariant.eq,
    read_discriminant, AspisR1PublicPreparation.transport.Variant.read_discriminant, folds]

theorem tag_result (v : V) :
    AspisR1PublicPreparation.transport.Variant.tag v =
      AspisR1.CheckpointBytes4Ops.tag (port v) := by
  cases v <;> rfl

theorem final_len_result (v : V) :
    AspisR1.CheckpointBytes4Ops.finalLen (port v) =
      ok (match v with | .S1 => 256#usize | .S2 => 64#usize | .D => 64#usize) := by
  cases v <;> rfl

theorem checkpoint_size_result (v : V) :
    AspisR1.CheckpointBytes4Ops.checkpointSize (port v) =
      ok (match v with | .S1 => 4840#usize | .S2 => 1768#usize | .D => 1768#usize) := by
  cases v <;> simp only [AspisR1.CheckpointBytes4Ops.checkpointSize,
    AspisR1.CheckpointBytes4Ops.finalLen, port, bind_tc_ok] <;>
    rw [AspisR1.Port4A_ReaderInstall.mul_value _ _ (by decide), bind_tc_ok,
      AspisR1.Port4A_ReaderInstall.add_value _ _ (by decide)] <;> rfl

#print axioms folds_result
#print axioms tag_result
#print axioms final_len_result
#print axioms checkpoint_size_result
end NFY_NBG_Transport
-- END copied NBG_Transport

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
