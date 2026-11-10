import NPP_ProbeDefs
set_option maxHeartbeats 0
/-! NPP_ timing probe driver (compiled only; run by NPP_Probe.lean). EXECUTABLE EVIDENCE, NOT A PROOF.
Target not yet established.

`#eval` in the Lean IR interpreter (no native_decide, no kernel reduction) of
`AdapterRw.r1_pool_adapter.owned.stage1_owned` at `NPP_Probe.sdkAt` (the computable copy of the
10 November host dictionary, `NPP_SdkNovEq.eq` and `NPP_Probe.sdkAt_eq`), on the recorded TX1 of
the 10 November devnet transfer (NPC_TRANSACTIONS record 35): program GqZzWuGT, the three
instruction accounts' pre-images and metas, instruction data 03 0a. H = `NPP_Probe.Hlog`
(SHA-256 in Lean, every query logged), pda := none, clock := ok 520606640, reservation := Ok (),
indexError := NFN_NEW_GeometryDictionary.err. The result is compared with the recorded
checkpoint post-image. -/
open AdapterRw Aeneas.Std NPP_Probe in
def NPP_Probe.main : IO Unit := do
  let dir := "/home/dombarker/project-offloads/codex-cx-nonvac-20261110/probe"
  let lines := ((← IO.FS.readFile (dir ++ "/accounts.txt")).splitOn "\n").filter (· ≠ "")
  let accs ← (List.range 3).mapM fun i => do
    let d ← IO.FS.readBinFile s!"{dir}/acc{i}.bin"
    pure (acct lines[i]! d)
  let program := key (NPP_Sha.unhex (← IO.FS.readFile (dir ++ "/program.txt")))
  let data := slice ((NPP_Sha.unhex (← IO.FS.readFile (dir ++ "/ixdata.txt"))).map u8)
  let post := (← IO.FS.readBinFile (dir ++ "/ckpt_post.bin")).toList.map (·.toNat)
  IO.println s!"NPP_PROBE inputs: accounts {accs.length}, data {data.val.length} bytes, expected checkpoint {post.length} bytes"
  let t0 ← IO.monoMsNow
  let r ← IO.lazyPure fun _ =>
    r1_pool_adapter.owned.stage1_owned (sdkAt Hlog pda0 clock0 res0 NFN_NEW_GeometryDictionary.err)
      program (slice accs) data
  let verdict := match r with
    | .ok (.Ok v) =>
      let got := vecBytes v
      if got == post then s!"Ok (Ok bytes): {got.length} bytes, EQUAL to the recorded checkpoint post-image"
      else
        let i := ((got.zip post).findIdx? fun (p : Nat × Nat) => p.1 != p.2).getD (min got.length post.length)
        s!"Ok (Ok bytes): {got.length} bytes, DIFFERENT from the recorded post-image (first difference at {i})"
    | .ok (.Err _) => "Ok (Err _): the model rejects the recorded TX1"
    | .fail _ => "fail: the model raised an Aeneas error"
    | .div => "div: the model diverged"
  IO.println s!"NPP_PROBE result: {verdict}"
  let t1 ← IO.monoMsNow
  IO.println s!"NPP_PROBE wall_ms {t1 - t0}"
