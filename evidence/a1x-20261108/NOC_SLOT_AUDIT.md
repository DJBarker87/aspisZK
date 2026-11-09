# NOC R1 slot audit and R2 allocation source

## R1 method (L009, L010; L010 is the complete run)

`NOC_SlotAudit` (diagnostic module; MetaM, no proof) builds, at an arbitrary host
context `c : NNH_HostCtx.Ctx W Tx`, the three dictionaries the A1/A2 paths execute:
`DrvC_Installation.currentInstalled (configuration c)` (22 slots),
`DrvC_Installation.sdk (configuration c)` (54 AdapterRw slots) and
`DrvC_Installation.stage (configuration c)` (25 VTop slots). Every slot is applied to fresh
variables and put in weak-head normal form. A residual of `NNH_HostSeed.m0` is
`fun .. => .div` (`by constructor <;> intros <;> exact .div`), so it reduces to head
`Aeneas.Std.Result.div`. Installed slots reduce to `ok`, a constant, or a stuck match
on a variable. Limitation: an installed slot whose body reaches a residual only
after a stuck match on its arguments would not be caught here; the reached
installed bodies were therefore also read (sources cited below).
L009 failed only on an unknown helper name in a trailing #print (the slot table it
printed for current and sdk is identical to L010's).

## R1 result: residual (`.div`) slots

| dictionary | slot | on A1 tx1 path? |
|---|---|---|
| current (AspisR1CurrentCaller.Ops) | op1 (allocation, `aspis_core::r0::heap::filled`) | YES: first call of `verifier.candidate.prepare` (087), reached from 094 `verifier.candidate.tx1` after k/op3/op4/mark/ZERO |
| stage (VTop_Stages.Ops) | op4, op7, op8, op12 | NO: the stage dictionary enters the sdk only through `Tx2I_Install.install` (`op11 := tx2_authenticated (stage base finish)`), the TX2 entry. Not audited for A2 reachability here; flagged to the A2 lane. |

All other slots of all three dictionaries are installed (table below).

## R1: slots reached by the installed tx1 path and how confirmed

345 `stage1_owned (sdk c)` (= NND_FreshStage1.fresh by rfl) and its helpers call sdk slots:
op1 (instruction-tag slice eq), op47 (public decode), op21 (validate), op24 (afterstate encode),
op0 (checkpoint slice eq), op35 (`OwnedAccount.data`, ProgramError clone), op36
(`require_distinct_accounts` loop, Pubkey eq), op12 (`require_verifier_checkpoint`), op44
(afterstate-bytes constant path), and through `first_decoded` (NND_FreshFirstDecoded.fresh):
op10 (current tx1), op43 (SolanaDigest digest), plus `observer` (= `ok none`, no slot).
Helper bodies were printed in L010 (DEF lines). All of these sdk slots are installed (table).
094 `verifier.candidate.tx1 (currentInstalled ..)` (NND_FreshTx1Source.fresh) calls current
op3, op4, op0 (ZERO), prepare (op15, op1, op10, op12, op13, op14, op11, op5, op9, op8, op2),
op20, op21, op6 (batch, installed by Op5T_Install.current; head is a stuck Result match), op19,
op18, op7, op17, op16. Only op1 is residual.

## Full table (slot, weak-head head)

```
AspisR1CurrentCaller.Ops.op0 Aeneas.Std.Result.ok
AspisR1CurrentCaller.Ops.op1 Aeneas.Std.Result.div
AspisR1CurrentCaller.Ops.op2 Aeneas.Std.Result.ok
AspisR1CurrentCaller.Ops.op3 Aeneas.Std.instReprResult.repr.match_1
AspisR1CurrentCaller.Ops.op4 Aeneas.Std.instReprResult.repr.match_1
AspisR1CurrentCaller.Ops.op5 Aeneas.Std.instReprResult.repr.match_1
AspisR1CurrentCaller.Ops.op6 Aeneas.Std.instReprResult.repr.match_1
AspisR1CurrentCaller.Ops.op7 Aeneas.Std.instReprResult.repr.match_1
AspisR1CurrentCaller.Ops.op8 Aeneas.Std.instReprResult.repr.match_1
AspisR1CurrentCaller.Ops.op9 AspisR1CurrentCaller.S1SemanticInstallation.install.match_1
AspisR1CurrentCaller.Ops.op10 Aeneas.Std.instReprResult.repr.match_1
AspisR1CurrentCaller.Ops.op11 Aeneas.Std.instReprResult.repr.match_1
AspisR1CurrentCaller.Ops.op12 Aeneas.Std.Result.ok
AspisR1CurrentCaller.Ops.op13 Aeneas.Std.Result.ok
AspisR1CurrentCaller.Ops.op14 Aeneas.Std.Result.ok
AspisR1CurrentCaller.Ops.op15 Aeneas.Std.Result.ok
AspisR1CurrentCaller.Ops.op16 Aeneas.Std.instReprResult.repr.match_1
AspisR1CurrentCaller.Ops.op17 Aeneas.Std.instReprResult.repr.match_1
AspisR1CurrentCaller.Ops.op18 Aeneas.Std.instReprResult.repr.match_1
AspisR1CurrentCaller.Ops.op19 Aeneas.Std.instReprResult.repr.match_1
AspisR1CurrentCaller.Ops.op20 Aeneas.Std.instReprResult.repr.match_1
AspisR1CurrentCaller.Ops.op21 Aeneas.Std.Result.ok
AdapterRw.Ops.op0 Decidable.rec
AdapterRw.Ops.op1 Decidable.rec
AdapterRw.Ops.op2 NNH_AdapterStd.optionEq.match_1
AdapterRw.Ops.op3 Aeneas.Std.Result.ok
AdapterRw.Ops.op4 Aeneas.Std.Result.ok
AdapterRw.Ops.op5 Aeneas.Std.Result.ok
AdapterRw.Ops.op6 Aeneas.Std.Result.ok
AdapterRw.Ops.op7 Aeneas.Std.Result.ok
AdapterRw.Ops.op8 Aeneas.Std.Result.ok
AdapterRw.Ops.op9 Aeneas.Std.Result.ok
AdapterRw.Ops.op10 AspisS6OuterNativeOps.resultMap.match_1
AdapterRw.Ops.op11 Aeneas.Std.instReprResult.repr.match_1
AdapterRw.Ops.op12 NGL_CheckpointModel.install.match_1
AdapterRw.Ops.op13 Aeneas.Std.Result.ok
AdapterRw.Ops.op14 Aeneas.Std.Result.ok
AdapterRw.Ops.op15 Aeneas.Std.instReprResult.repr.match_1
AdapterRw.Ops.op16 Aeneas.Std.Result.ok
AdapterRw.Ops.op17 Aeneas.Std.instReprResult.repr.match_1
AdapterRw.Ops.op18 Aeneas.Std.Result.ok
AdapterRw.Ops.op19 Aeneas.Std.Result.ok
AdapterRw.Ops.op20 NMS_RequestModels.nullifier.match_1
AdapterRw.Ops.op21 AspisR1.NNH_S1HostCodec.validate.match_1
AdapterRw.Ops.op22 AspisS6OuterNativeOps.resultMap.match_1
AdapterRw.Ops.op23 Aeneas.Std.instReprResult.repr.match_1
AdapterRw.Ops.op24 AspisR1.NNH_S1HostCodec.encode.match_1
AdapterRw.Ops.op25 Aeneas.Std.Result.ok
AdapterRw.Ops.op26 Aeneas.Std.Result.ok
AdapterRw.Ops.op27 Aeneas.Std.Result.ok
AdapterRw.Ops.op28 Aeneas.Std.Result.ok
AdapterRw.Ops.op29 Aeneas.Std.Result.ok
AdapterRw.Ops.op30 Aeneas.Std.Result.ok
AdapterRw.Ops.op31 NJQ_Canonical.mapOuter.match_1
AdapterRw.Ops.op32 NJQ_Canonical.mapOuter.match_1
AdapterRw.Ops.op33 Aeneas.Std.instReprResult.repr.match_1
AdapterRw.Ops.op34 Aeneas.Std.instReprResult.repr.match_1
AdapterRw.Ops.op35 Aeneas.Std.Result.ok
AdapterRw.Ops.op36 Aeneas.Std.Result.ok
AdapterRw.Ops.op37 Aeneas.Std.Result.ok
AdapterRw.Ops.op38 Aeneas.Std.Result.ok
AdapterRw.Ops.op39 Aeneas.Std.Result.ok
AdapterRw.Ops.op40 Aeneas.Std.Result.ok
AdapterRw.Ops.op41 Aeneas.Std.Result.ok
AdapterRw.Ops.op42 Aeneas.Std.Result.ok
AdapterRw.Ops.op43 Aeneas.Std.Result.ok
AdapterRw.Ops.op44 Aeneas.Std.Result.ok
AdapterRw.Ops.op45 Aeneas.Std.Result.ok
AdapterRw.Ops.op46 Aeneas.Std.Result.ok
AdapterRw.Ops.op47 Aeneas.Std.instReprResult.repr.match_1
AdapterRw.Ops.op48 NJQ_Canonical.mapOuter.match_1
AdapterRw.Ops.op49 NJQ_Canonical.mapOuter.match_1
AdapterRw.Ops.op50 Aeneas.Std.instReprResult.repr.match_1
AdapterRw.Ops.op51 AspisR1.NFY_JHf_Scan.source.match_1
AdapterRw.Ops.op52 Aeneas.Std.instReprResult.repr.match_1
AdapterRw.Ops.op53 Aeneas.Std.instReprResult.repr.match_1
VTop_Stages.Ops.op0 Aeneas.Std.Result.ok
VTop_Stages.Ops.op1 Aeneas.Std.Result.ok
VTop_Stages.Ops.op2 Decidable.rec
VTop_Stages.Ops.op3 Aeneas.Std.instReprResult.repr.match_1
VTop_Stages.Ops.op4 Aeneas.Std.Result.div
VTop_Stages.Ops.op5 Aeneas.Std.instReprResult.repr.match_1
VTop_Stages.Ops.op6 Aeneas.Std.instReprResult.repr.match_1
VTop_Stages.Ops.op7 Aeneas.Std.Result.div
VTop_Stages.Ops.op8 Aeneas.Std.Result.div
VTop_Stages.Ops.op9 Aeneas.Std.instReprResult.repr.match_1
VTop_Stages.Ops.op10 Aeneas.Std.instReprResult.repr.match_1
VTop_Stages.Ops.op11 Aeneas.Std.instReprResult.repr.match_1
VTop_Stages.Ops.op12 Aeneas.Std.Result.div
VTop_Stages.Ops.op13 AspisR1.Port1_LibrarySource.mark.match_1
VTop_Stages.Ops.op14 Aeneas.Std.Result.ok
VTop_Stages.Ops.op15 Aeneas.Std.Result.ok
VTop_Stages.Ops.op16 Aeneas.Std.Result.ok
VTop_Stages.Ops.op17 Aeneas.Std.instReprResult.repr.match_1
VTop_Stages.Ops.op18 Aeneas.Std.instReprResult.repr.match_1
VTop_Stages.Ops.op19 Aeneas.Std.instReprResult.repr.match_1
VTop_Stages.Ops.op20 Aeneas.Std.Result.ok
VTop_Stages.Ops.op21 Aeneas.Std.Result.ok
VTop_Stages.Ops.op22 Aeneas.Std.Result.ok
VTop_Stages.Ops.op23 Aeneas.Std.Result.ok
VTop_Stages.Ops.unwrap32 AspisR1.Port4B_FoldedCut.unwrap32.match_1
```

## R2: what the frozen Rust does at the op1 call

Pinned revision: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387` (the revision recorded in
evidence/extract-stage-20261106/NHR_E001/sources/NHR_STAGING_MANIFEST.json). The extracted
Aeneas source evidence/extract-stage-20261106/NHR_emitted/prepare/raw/NHR_prepare/Funs.lean:173
calls `aspis_core.r0.heap.filled core.marker.CopyU8 i2 0#u8`, and NHR_OPACITY.json lists
`aspis_core::r0::heap::filled` as an OPAQUE boundary ("Existing allocation boundary; retains full
Result and allocation trust"). So the Aeneas source fixes the call and its full Result type but
not its body; the body is the Rust source at the pin:

- crates/aspis-r1-cost-probe/src/candidate.rs:255-256 (rev 4bb3b3f):
  `let mut logical = aspis_core::r0::heap::filled(compact::LOGICAL_SEMANTIC + compact::LOGICAL_Y1, 0u8).map_err(|_| Error::Allocation)?;`
- crates/aspis-core/src/r0/heap.rs:5-10 (blob ef7826d856274ff9a8347e11c15f04b302f440fd,
  sha256 67153a3f..., identical in the manifest and on research):
  `pub fn filled<T: Copy>(n: usize, value: T) -> Result<Vec<T>, Error> { let mut out = Vec::new();
   out.try_reserve_exact(n).map_err(|_| Error::Allocation)?; out.resize(n, value); Ok(out) }`

So the call returns `Ok(vec![0u8; 14759])` when the exact reservation succeeds and
`Err(Error::Allocation)` otherwise (then mapped to verifier `Error::Allocation`). It never
diverges and has no other outcome.

`LIB_VLib.filledValue = LIBC_Filled.value n env = if env.reservation then .ok (List.replicate n 0)
else .error ()` (evidence/libc-20261111/LIBC_Filled.lean) is a faithful model of this call,
on the standing interpretation that the reservation outcome is the environment's single
allocator bit `env.reservation` (the existing Solana-runtime allocator trust row, shared with
the Claims and accumulator allocations; LIB_VLib.reservation_functional). The error payload is
discarded, which is sound because the caller maps every Err to Allocation. Its native
counterpart `OraclePortStdAllocation.filled n x reserved` is linked by `LIBC_Filled.model`.

Note: `JGp_Allocation.filled` passes the literal `true` as the reservation, i.e. it models
only the successful allocator. It is not faithful when the reservation fails. R3 therefore
installs the same `OraclePortStdAllocation.filled` model with the configuration's own
reservation bit instead of `true`.
