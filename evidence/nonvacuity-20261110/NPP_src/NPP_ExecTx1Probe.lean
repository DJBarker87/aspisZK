import NPP_ExecTx1
import NPP_ProbeDefs
set_option maxHeartbeats 0
/-! NPP_ EXECUTABLE-ONLY probe of tx1Value (code generated from equation lemmas and definition
values, not kernel-checked; never a theorem). Target not yet established.

`NPP_X.NNH_ReturnsBundle.tx1Value ⟨key program, accounts xs, bytes data⟩ env` on the recorded TX1
of the 10 November transfer (record 35): the arguments in the form of `NOC_Stage1Iff.iff345`, and
`env = DGP_HostDigest.envInst H pda clock reservation`. H looks up the saved TX1 query table
(NPP_L012/NPP_H_TABLE.tsv); a miss is computed by the Lean SHA-256 and logged (`NPP_QMISS`). The
expected value is `iff345`'s right-hand side, `.ok (bytes saved.deref)` with `saved` the recorded
checkpoint post-image. -/
namespace NPP_ExecProbe
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def Htab (m : Std.HashMap String String) (q : Bytes) : State :=
  let ba := NPP_Probe.toBA q
  let qh := NPP_Sha.hex ba
  match m.get? qh with
  | some d =>
    let db := NPP_Sha.unhex d
    fun i => ⟨(db.getD i.val 0).toNat % 256, Nat.mod_lt _ (by decide)⟩
  | none =>
    dbgTrace s!"NPP_QMISS {qh}" fun _ => NPP_Probe.Hlog q
end NPP_ExecProbe

open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier NPP_ExecProbe in
unsafe def NPP_ExecProbe.main : IO Unit := do
  let dir := "/home/dombarker/project-offloads/codex-cx-nonvac-20261110/probe"
  let tab := ((← IO.FS.readFile (dir ++ "/H_TABLE.tsv")).splitOn "\n").filter (· ≠ "")
  let m : Std.HashMap String String := tab.foldl (fun m l => match l.splitOn "\t" with
    | [q, d] => m.insert q d | _ => m) {}
  let lines := ((← IO.FS.readFile (dir ++ "/accounts.txt")).splitOn "\n").filter (· ≠ "")
  let accs ← (List.range 3).mapM fun i => do
    let d ← IO.FS.readBinFile s!"{dir}/acc{i}.bin"
    pure (NPP_Probe.acct lines[i]! d)
  let program := NPP_Probe.key (NPP_Sha.unhex (← IO.FS.readFile (dir ++ "/program.txt")))
  let data := NPP_Probe.slice ((NPP_Sha.unhex (← IO.FS.readFile (dir ++ "/ixdata.txt"))).map NPP_Probe.u8)
  let post := (← IO.FS.readBinFile (dir ++ "/ckpt_post.bin")).toList.map NPP_Probe.u8
  let saved := NPP_Probe.vec post
  IO.println s!"NPP_EXEC_TX1 table entries {m.size}"
  let env := DGP_HostDigest.envInst (Htab m) NPP_Probe.pda0 NPP_Probe.clock0 NPP_Probe.res0
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure fun _ => NPP_X.NNH_ReturnsBundle.tx1Value ⟨key program, accounts (NPP_Probe.slice accs), bytes data⟩ env
  let expected := bytes saved.deref
  let verdict := match r with
    | .ok b => if b == expected then s!"ok bytes: {b.length} bytes, EQUAL to the recorded checkpoint post-image (iff345 right-hand side)"
               else s!"ok bytes: {b.length} bytes, DIFFERENT from the recorded post-image"
    | .error _ => "error: the RSL reference model rejects the recorded TX1"
  IO.println s!"NPP_EXEC_TX1 result: {verdict}"
  IO.println s!"NPP_EXEC_TX1 wall_ms {(← IO.monoMsNow) - t0}"

#eval NPP_ExecProbe.main
