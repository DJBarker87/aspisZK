import S2A_InstalledCuts

/-! Installed PURE value contracts. This module supplies neither native allocation
semantics nor a native state/effect frame. Outer fail/div are retained. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2G
open AspisS2OwnedStage1 AspisS2OwnedStage1.SdkReference
abbrev Statement := ReadyStatement.Statement
abbrev Afterstate := aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev PE := solana_program_error.ProgramError

/-- The actual caller's format-error map, retaining outer failure/divergence. -/
def mapFormat {A E : Type} (r : Result (core.result.Result A E)) :
    Result (core.result.Result A PE) := do
  let reply ← r
  match reply with
  | .Ok a => ok (.Ok a)
  | .Err _ => ok (.Err .InvalidAccountData)

theorem mapFormat_success {A E : Type} (r : Result (core.result.Result A E)) (a : A)
    (h : mapFormat r = ok (.Ok a)) : r = ok (.Ok a) := by
  cases r with
  | fail e => cases h
  | div => cases h
  | ok reply => cases reply with
    | Err e => cases h
    | Ok b => cases h; rfl

def decode (ops : SdkReference.Ops) (vops : AspisR1CurrentCaller.Ops) (b : Slice U8) :=
  SdkReference.decode_public_statement_box (Installation.install ops vops) b

def validate (s : Statement) := mapFormat (SourceInstallation.actualValidator s)
def candidate (a : Afterstate) := mapFormat (SourceInstallation.actualEncoder a)

def first (ops : SdkReference.Ops) (vops : AspisR1CurrentCaller.Ops)
    (s : Statement) (publicInput proof : Slice U8) (split : Usize) :=
  SdkReference.first_decoded (Installation.install ops vops)
    (ReadyStatement.publicOf s) publicInput proof split

/-- No success/length premise for the later validator is added. -/
theorem decode_contract (ops : SdkReference.Ops) (vops : AspisR1CurrentCaller.Ops)
    (b : Slice U8) (s : Statement) (h : decode ops vops b = ok (.Ok s)) :
    b.val.length = 1880 ∧ validate s = ok (.Ok ()) ∧
    ∃ decoded : AspisR1TerminalDecoder.PublicBinding.Statement,
      AspisR1PublicPreparation.S6DecoderScopedReuseV1.decodeActual b = ok (.Ok decoded) ∧
      s = CurrentCarrier.fromDecoderStatement decoded := by
  obtain ⟨decoded,actual,same,length,validated⟩ := S2A.InstalledCuts.decoded ops vops b s h
  refine ⟨length,?_,decoded,actual,same⟩
  change SourceInstallation.actualValidator s = ok (.Ok ()) at validated
  simp only [validate,mapFormat,validated,bind_tc_ok]

/-- Exact existing validator observation; no extra validity predicate assumed. -/
theorem validate_contract (s : Statement) (h : validate s = ok (.Ok ())) :
    SourceInstallation.actualValidator s = ok (.Ok ()) := mapFormat_success _ _ h

/-- Exact encoder return on the field-preserving carrier. Array width is 688;
no unproved canonicality, totality or native frame is appended. -/
theorem candidate_contract (a : Afterstate) (bytes : Array U8 688#usize)
    (h : candidate a = ok (.Ok bytes)) :
    AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1
      (CurrentCarrier.toDecoderAfterstate a) = ok (.Ok bytes) := by
  have actual := mapFormat_success _ _ h
  unfold SourceInstallation.actualEncoder at actual
  cases run : AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1
      (CurrentCarrier.toDecoderAfterstate a) with
  | fail e => simp only [run,bind_tc_fail] at actual; cases actual
  | div => simp only [run,bind_tc_div] at actual; cases actual
  | ok reply =>
    cases reply with
    | Err e => simp only [run,bind_tc_ok] at actual; cases actual
    | Ok out => simp only [run,bind_tc_ok] at actual; cases actual; exact run

/-- Returns THIS checkpoint from current tx1 with release observer None.
No child-wide checkpoint-length or frozen-verifier equivalence is asserted. -/
theorem first_contract (ops : SdkReference.Ops) (vops : AspisR1CurrentCaller.Ops)
    (s : Statement) (publicInput proof : Slice U8) (split : Usize) (cp : alloc.vec.Vec U8)
    (h : first ops vops s publicInput proof split = ok (.Ok cp)) :
    AspisR1CurrentCaller.verifier.candidate.tx1 vops
      (SourceInstallation.currentDigest
        (SolanaDigest.Insts.Aspis_coreDigestDigest32 (Installation.install ops vops)))
      (CurrentCarrier.toCurrentPublic (ReadyStatement.publicOf s)) publicInput proof split () none =
        ok (.Ok cp) := Installation.first_success ops vops _ _ _ _ cp h

#print axioms mapFormat_success
#print axioms decode_contract
#print axioms validate_contract
#print axioms candidate_contract
#print axioms first_contract
end AspisR1.S2G
