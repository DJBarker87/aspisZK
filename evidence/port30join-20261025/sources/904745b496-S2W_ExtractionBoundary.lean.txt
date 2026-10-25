import S2W_FinalAudit
import S2X_SecondCut

/-! D188: correspondence of the owned Rust functions to the extracted source
semantics is a named project trust item. It is not an S2 source-proof goal.
Non-extracted AccountInfo wrappers are deliberately outside this record. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_ExtractionBoundary
open Aeneas Aeneas.Std Result
open AspisR1.AdapterRw MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
abbrev Accounts := Slice Cuts.Account
abbrev Program := AdapterRw.solana_pubkey.Pubkey
abbrev Slot := core.result.Result U64 Cuts.PE
abbrev First := Program → Accounts → Slice U8 → Result (core.result.Result (alloc.vec.Vec U8) Cuts.PE)
abbrev Second := Program → Accounts → Slice U8 → Slot → Result (core.result.Result Unit Cuts.PE)

/-- Exactly the project extraction boundary, including the extracted digest
installation. No account frame, site observation, accepted result, input-buffer
identity, checkpoint persistence, or caller-facts proposition is a field.
Binary correspondence remains rustc/P7 and S10, outside this source theorem. -/
structure AeneasExtraction (ops : AdapterRw.Ops) (native1 : First) (native2 : Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) : Prop where
  stage1 : ∀ program accounts data,
    native1 program accounts data = AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data
  stage2 : ∀ program accounts data slot,
    native2 program accounts data slot = AdapterRw.r1_pool_adapter.owned.stage2_owned ops program accounts data slot
  digest : ∀ self parts, ops.op43 self parts = hashv parts

/-- P1 and RuntimeSyscall are separately named records; neither assumes the
caller's oracle field, source acceptance, or a returning-domain restriction. -/
structure P1 (sha256 H : Bytes → State) : Prop where
  realization : S2Z.Oracle.P1Realization sha256 H
structure RuntimeSyscall (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (sha256 : Bytes → State) : Prop where
  returningValue : S2Z.Oracle.RuntimeSyscall hashv sha256

/-- Every accepted pair of the native owned entry functions has ONE exact
ordered source observation, with the actual typed calls/arguments/returns.
Both accepted executions use the SAME Ops. Internal child events are still
provided by the separately named child cone joins, as D188 requires. -/
theorem accepted_native_observation (ops : AdapterRw.Ops) (native1 : First) (native2 : Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : AeneasExtraction ops native1 native2 hashv)
    (program : Program) (accounts1 accounts2 : Accounts) (data1 data2 : Slice U8)
    (slot : Slot) (checkpoint : alloc.vec.Vec U8)
    (accepted1 : native1 program accounts1 data1 = ok (.Ok checkpoint))
    (accepted2 : native2 program accounts2 data2 slot = ok (.Ok ())) :
    ∃ firstLog finalLog suffix,
      S2W_Trace.run ops (S2W_Outer.stage1_owned ops S2W_Outer.traceEffects program accounts1 data1)
        [] = ok (.Ok checkpoint,firstLog) ∧
      S2W_Trace.run ops (S2W_Outer.stage2_owned ops S2W_Outer.traceEffects program accounts2 data2 slot)
        firstLog = ok (.Ok (),finalLog) ∧
      S2W_Trace.run ops (S2W_Observation.two ops program accounts1 data1 accounts2 data2 slot) [] =
        ok (.Ok checkpoint,finalLog) ∧
      finalLog = firstLog ++ suffix ∧
      (∀ e ∈ finalLog, S2W_TraceFacts.ValidEvent ops e) := by
  rw [extraction.stage1] at accepted1
  rw [extraction.stage2] at accepted2
  obtain ⟨firstLog,finalLog,suffix,first,second,both,extension⟩ :=
    S2W_Observation.accepted_segments ops program accounts1 data1 accounts2 data2 slot checkpoint
      accepted1 accepted2
  exact ⟨firstLog,finalLog,suffix,first,second,both,extension,
    S2W_TraceFacts.run_valid ops _ [] finalLog _ (by simp) both⟩

/-- NativeBinding is discharged by the named extraction boundary, not retained
as another S2 premise. No totality is introduced, including for multiproof. -/
theorem native_oracle (ops : AdapterRw.Ops) (native1 : First) (native2 : Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : AeneasExtraction ops native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : P1 sha256 H) (runtime : RuntimeSyscall hashv sha256) :
    CheckpointBytes5Inputs.Oracle (S2Z.Oracle.leadDigest ops) () H :=
  S2W_SuccessOracle.native_success_field ops hashv sha256 H extraction.digest
    runtime.returningValue p1.realization

/-- Actual native TX1 call arguments, proofLength and proofSuffix, now with
no residual owned-native association obligation. The nine-site projection is
not identified with an independently supplied Inputs record. -/
theorem native_first_fields (ops : AdapterRw.Ops) (native1 : First) (native2 : Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : AeneasExtraction ops native1 native2 hashv)
    (program : Program) (accounts : Accounts) (data : Slice U8)
    (checkpoint : alloc.vec.Vec U8)
    (accepted : native1 program accounts data = ok (.Ok checkpoint)) :
    ∃ proofAccount publicAccount publicInput raw statement semantic proof split,
      Slice.index_usize accounts 0#usize = ok proofAccount ∧
      Slice.index_usize accounts 1#usize = ok publicAccount ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops proofAccount = ok (.Ok raw) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops publicAccount = ok (.Ok publicInput) ∧
      ops.op47 publicInput = ok (.Ok statement) ∧
      AdapterRw.first_decoded ops semantic publicInput proof split = ok (.Ok checkpoint) ∧
      (bytesOf proof.val).length = 57607 ∧
      bytesOf raw.val = (bytesOf raw.val).take 688 ++ bytesOf proof.val := by
  rw [extraction.stage1] at accepted
  exact LeadInputs.first_byte_fields ops program accounts data checkpoint accepted

#print axioms accepted_native_observation
#print axioms native_oracle
#print axioms native_first_fields
#print AeneasExtraction
#print P1
#print RuntimeSyscall
end AspisR1.S2W_ExtractionBoundary
end
