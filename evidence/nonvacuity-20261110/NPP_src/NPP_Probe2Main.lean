import NPP_ProbeDefs
set_option maxHeartbeats 0
/-! Solana `create_program_address` in Lean, used only as the executable pda binder of the TX2 probe:
sha256(seeds ‖ program ‖ "ProgramDerivedAddress"), rejected (none) if more than 16 seeds, a seed
longer than 32 bytes, or the digest decompresses to an ed25519 point (u/v a square mod p, with
y the little-endian digest with bit 255 cleared, u = y²-1, v = d·y²+1; curve25519-dalek
`CompressedEdwardsY::decompress`). Every query is logged as `NPP_PDA <seeds> <program> <answer>`;
NPP_check_pda.py recomputes each one. -/
namespace NPP_Pda
def p : Nat := 2 ^ 255 - 19
def d : Nat := 37095705934669439343138083508754565189542113879843219016388785533085940283555
def powMod (b e m : Nat) : Nat := Id.run do
  let mut r := 1; let mut x := b % m; let mut k := e
  for _ in [0:256] do
    if k % 2 == 1 then r := r * x % m
    x := x * x % m; k := k / 2
  return r
def onCurve (h : ByteArray) : Bool :=
  let y0 := (List.range 32).foldr (fun i acc => acc * 256 + (h.get! i).toNat) 0
  let y := (y0 % 2 ^ 255) % p
  let y2 := y * y % p
  let u := (y2 + p - 1) % p
  let v := (d * y2 + 1) % p
  let r := u * powMod v (p - 2) p % p
  let l := powMod r ((p - 1) / 2) p
  l == 0 || l == 1
def create (seeds : List (List UInt8)) (prog : List UInt8) : Option (List UInt8) :=
  if seeds.length > 16 || seeds.any (·.length > 32) then none else
  let msg := (seeds.foldl (· ++ ·) []) ++ prog ++ "ProgramDerivedAddress".toUTF8.toList
  let h := NPP_Sha.hash ⟨msg.toArray⟩
  if onCurve h then none else some h.toList
end NPP_Pda

/-! NPP_ TX2 timing probe driver (compiled only; run by NPP_Probe2.lean). EXECUTABLE EVIDENCE, NOT A
PROOF. Target not yet established.

`AdapterRw.r1_pool_adapter.owned.stage2_owned` at the computable 10 November dictionary
`NPP_Probe.sdkAt` on the verifier CPI of the recorded TX2 (NPC_TRANSACTIONS record 36): the CPI's 7
accounts in CPI order with their TX2 pre-images (signer/writable from the outer message flags), the
CPI's 320-byte instruction data, current_slot := Ok 520606678. H = `NPP_Probe.Hlog` (logged).
The dictionary's final call `op53 statement` (the return of the accepted statement) is wrapped to log
`op22 statement` (the statement's 1880-byte encoding) as `NPP_OP53 <hex>`; the wrapper calls the
unchanged `op53`. -/
open AdapterRw Aeneas.Std in
def NPP_Probe.errName : solana_program_error.ProgramError → String
  | .Custom c => s!"Custom {c.bv.toNat}"
  | .InvalidArgument => "InvalidArgument"
  | .InvalidInstructionData => "InvalidInstructionData"
  | .InvalidAccountData => "InvalidAccountData"
  | .AccountDataTooSmall => "AccountDataTooSmall"
  | .InsufficientFunds => "InsufficientFunds"
  | .IncorrectProgramId => "IncorrectProgramId"
  | .MissingRequiredSignature => "MissingRequiredSignature"
  | .AccountAlreadyInitialized => "AccountAlreadyInitialized"
  | .UninitializedAccount => "UninitializedAccount"
  | .NotEnoughAccountKeys => "NotEnoughAccountKeys"
  | .AccountBorrowFailed => "AccountBorrowFailed"
  | .MaxSeedLengthExceeded => "MaxSeedLengthExceeded"
  | .InvalidSeeds => "InvalidSeeds"
  | .BorshIoError m => s!"BorshIoError {m}"
  | .AccountNotRentExempt => "AccountNotRentExempt"
  | .UnsupportedSysvar => "UnsupportedSysvar"
  | .IllegalOwner => "IllegalOwner"
  | .MaxAccountsDataAllocationsExceeded => "MaxAccountsDataAllocationsExceeded"
  | .InvalidRealloc => "InvalidRealloc"
  | .MaxInstructionTraceLengthExceeded => "MaxInstructionTraceLengthExceeded"
  | .BuiltinProgramsMustConsumeComputeUnits => "BuiltinProgramsMustConsumeComputeUnits"
  | .InvalidAccountOwner => "InvalidAccountOwner"
  | .ArithmeticOverflow => "ArithmeticOverflow"
  | .Immutable => "Immutable"
  | .IncorrectAuthority => "IncorrectAuthority"

/-- pda binder: `NPP_Pda.create`, every query logged. -/
def NPP_Probe.pdaLog (seeds : List RSL.Bytes) (prog : RSL.B32) : Option RSL.B32 :=
  let ans := NPP_Pda.create seeds prog.bytes
  let out : Option RSL.B32 := match ans with
    | some l => if h : l.length = 32 then some ⟨l, h⟩ else none
    | none => none
  dbgTrace s!"NPP_PDA {(seeds.map fun b => NPP_Sha.hex ⟨b.toArray⟩)} {NPP_Sha.hex ⟨prog.bytes.toArray⟩} {(ans.map fun l => NPP_Sha.hex ⟨l.toArray⟩).getD "none"}" fun _ => out

open AdapterRw Aeneas.Std in
def NPP_Probe.enc22 (base : AdapterRw.Ops)
    (st : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) : String :=
  match base.op22 st with
  | .ok (.Ok a) => NPP_Sha.hex ⟨(a.val.map fun x => x.bv.toNat.toUInt8).toArray⟩
  | .ok (.Err _) => "op22-Err"
  | _ => "op22-not-ok"

open AdapterRw Aeneas.Std in
def NPP_Probe.log53 (base : AdapterRw.Ops)
    (st : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) :
    Aeneas.Std.Result (core.result.Result Unit solana_program_error.ProgramError) :=
  dbgTrace s!"NPP_OP53 {NPP_Probe.enc22 base st}" fun _ => base.op53 st

open AdapterRw Aeneas.Std NPP_Probe in
def NPP_Probe.main2 : IO Unit := do
  let dir := "/home/dombarker/project-offloads/codex-cx-nonvac-20261110/probe2"
  let lines := ((← IO.FS.readFile (dir ++ "/accounts.txt")).splitOn "\n").filter (· ≠ "")
  let accs ← (List.range 7).mapM fun i => do
    let d ← IO.FS.readBinFile s!"{dir}/acc{i}.bin"
    pure (acct lines[i]! d)
  let program := key (NPP_Sha.unhex (← IO.FS.readFile (dir ++ "/program.txt")))
  let data := slice ((NPP_Sha.unhex (← IO.FS.readFile (dir ++ "/ixdata.txt"))).map u8)
  let slotN := (← IO.FS.readFile (dir ++ "/slot.txt")).trim.toNat!
  let slot : core.result.Result U64 solana_program_error.ProgramError :=
    if h : slotN < 2 ^ UScalarTy.U64.numBits then .Ok (UScalar.ofNatCore slotN h) else .Ok 0#u64
  IO.println s!"NPP_PROBE2 inputs: accounts {accs.length}, data {data.val.length} bytes, slot {slotN}"
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure fun _ =>
    let base := sdkAt Hlog pdaLog (.ok 520606678) res0 NFN_NEW_GeometryDictionary.err
    let sdk : AdapterRw.Ops := { base with op53 := NPP_Probe.log53 base }
    r1_pool_adapter.owned.stage2_owned sdk program (slice accs) data slot
  let verdict := match r with
    | .ok (.Ok ()) => "Ok (Ok ()): the model accepts the recorded TX2 verifier CPI"
    | .ok (.Err e) => s!"Ok (Err {errName e}): the model rejects the recorded TX2 verifier CPI"
    | .fail _ => "fail: the model raised an Aeneas error"
    | .div => "div: the model diverged"
  IO.println s!"NPP_PROBE2 result: {verdict}"
  let t1 ← IO.monoMsNow
  IO.println s!"NPP_PROBE2 wall_ms {t1 - t0}"
