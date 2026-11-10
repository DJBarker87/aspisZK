import NPP_ExecTx2
import NPP_Probe2Main
set_option maxHeartbeats 0
/-! NPP_ EXECUTABLE-ONLY probe of tx2Value (code generated from equation lemmas and definition
values, not kernel-checked; never a theorem). Target not yet established.

`NPP_X.NNH_ReturnsBundle.tx2Value ⟨key program, accounts xs, bytes data, reply slot current_slot⟩ env`
on the verifier CPI of the recorded TX2 (record 36): program GqZzWuGT, the CPI's 7 accounts in CPI
order with TX2 pre-images and the Pool's CPI privileges (read-only, non-signer; pair_forest_dispatch.rs
320-338), the 320-byte ASQ8 data, current_slot Ok 520606678. env = envInst H pda clock reservation,
with H the saved TX2 query table (NPP_L037; misses computed and logged), pda the logged Lean
`create_program_address` (NPP_Pda), clock ok 520606678. The recorded verifier CPI succeeded, so the
expected value is `.ok ()`. -/
namespace NPP_ExecProbe2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
def Htab (m : Std.HashMap String String) (q : Bytes) : State :=
  let ba := NPP_Probe.toBA q
  let qh := NPP_Sha.hex ba
  match m.get? qh with
  | some d =>
    let db := NPP_Sha.unhex d
    fun i => ⟨(db.getD i.val 0).toNat % 256, Nat.mod_lt _ (by decide)⟩
  | none => dbgTrace s!"NPP_QMISS {qh}" fun _ => NPP_Probe.Hlog q
end NPP_ExecProbe2

open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier NPP_ExecProbe2 in
unsafe def NPP_ExecProbe2.main : IO Unit := do
  let dir := "/home/dombarker/project-offloads/codex-cx-nonvac-20261110/probe2"
  let tab := ((← IO.FS.readFile (dir ++ "/H_TABLE.tsv")).splitOn "\n").filter (· ≠ "")
  let m : Std.HashMap String String := tab.foldl (fun m l => match l.splitOn "\t" with
    | [q, d] => m.insert q d | _ => m) {}
  let lines := ((← IO.FS.readFile (dir ++ "/accounts.txt")).splitOn "\n").filter (· ≠ "")
  let accs ← (List.range 7).mapM fun i => do
    let d ← IO.FS.readBinFile s!"{dir}/acc{i}.bin"
    pure (NPP_Probe.acct lines[i]! d)
  let program := NPP_Probe.key (NPP_Sha.unhex (← IO.FS.readFile (dir ++ "/program.txt")))
  let data := NPP_Probe.slice ((NPP_Sha.unhex (← IO.FS.readFile (dir ++ "/ixdata.txt"))).map NPP_Probe.u8)
  let slotN := (← IO.FS.readFile (dir ++ "/slot.txt")).trim.toNat!
  let slotR : core.result.Result U64 solana_program_error.ProgramError :=
    if h : slotN < 2 ^ UScalarTy.U64.numBits then .Ok (UScalar.ofNatCore slotN h) else .Ok 0#u64
  IO.println s!"NPP_EXEC_TX2 table entries {m.size}, accounts {accs.length}, data {data.val.length}"
  let env := DGP_HostDigest.envInst (Htab m) NPP_Probe.pdaLog (.ok 520606678) NPP_Probe.res0
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure fun _ => NPP_X.NNH_ReturnsBundle.tx2Value
    ⟨key program, accounts (NPP_Probe.slice accs), bytes data, reply slot slotR⟩ env
  let verdict := match r with
    | .ok () => "ok (): the RSL reference model accepts the recorded TX2 verifier CPI (the recorded outcome)"
    | .error _ => "error: the RSL reference model rejects the recorded TX2 verifier CPI"
  IO.println s!"NPP_EXEC_TX2 result: {verdict}"
  IO.println s!"NPP_EXEC_TX2 wall_ms {(← IO.monoMsNow) - t0}"

#eval NPP_ExecProbe2.main
