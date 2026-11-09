# NOC A1 handoff (Claude worker replacing NNX)

No A1 field term is delivered. Target not yet established.

Scopes: 8 of 30 used (6 pass, 2 fail); 0 Kani, 0 extraction. Every scope ran
under the NNX caps (MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64,
`lake env lean -j1 -M7000 -DElab.async=false`, 180 s), admission allowed:true,
share count 0 and whole-host lean count 0 at each launch, disk free above 40 GB.
Exact target, exit, wall, peak RSS, swap, revision and printed axioms per scope
are in NOC_COMPILE.tsv; receipts in NOC_L00x/receipt.json; client NOC_run.py
(NNX_run.py with prefix NOC, budget 30, plus a whole-host lean count check).
No cap, heartbeat, timeout or recursion limit was raised. No sorry, axiom or
native_decide in any accepted module; every printed root is standard-only
(propext, Classical.choice, Quot.sound, or none).

Failures: L001 (NOC_FinishSource) was a tactic-macro layout parse error, so the
proof never ran (log shows sorryAx; counted as a failure). Fixed by single-line
macros, checked locally against core Lean v4.32.0 with a toy file, then L002
passed. L007 (NOC_PrepareDiv) failed only on `29#usize * 32#usize = ok 928#usize`
by rfl (platform-sized Usize); L008 uses the checked-multiplication lemma
UsizeArithmetic.mul_eq_ok instead.

## X3 closed (4 scopes, L001-L004)

The exact open goal of NNV_REMAINING/NNX_REMAINING is now a theorem:

```lean
theorem AspisR1.NOC_Op9.op9 {W Tx : Type} (c : Ctx W Tx) (pub : NNH_Libraries.VL.Public)
 (bytes : Slice U8) (sem : RSL.Verified NNH_Libraries.VL) :
 NNH_ObservedReturns.value ⟨pub, LIB_Carriers.bytes bytes⟩ (envOf c) = .ok sem →
 (DrvC_Installation.currentInstalled (configuration c)).op9
  (NNV_PreparedAtHost.digest c)
  (AspisR1CurrentCaller.FirstComposition.toCurrentPublic pub) bytes () none =
 .ok (.Ok (NNV_PreparedInputs.sem sem))
```
No hypothesis beyond the SAME returned observed value. Join, each a full Result
equality in its own small module:
- `NOC_FinishSource.source` (L002): `FinishModel.finish AspisS1ExtractedRoundChildren.children Bi
  (LIB_VCode.digest env) a.public_ (prefixRaw a.prefix_) a.transcript (challengesRaw a.challenges) none
  = .ok (.Ok (LIBC_PreparedCarriers.verified LIB_Prepared.types sem))` from
  `NNH_FinishReturns.value a env = .ok sem`, with `Bi` the literal installed
  boundaries `S1SemanticRootCopy.install (ClaimsUnrolledFinish.install (NP6_StdModel.calls (.Ok ()))
  (IDa_Deployed.boundaries (.Ok ())))`. Technique: `step` (one bind stepped by a
  port equality unified up to definitional equality, never by syntactic rewrite)
  plus pure normalization through `Aeneas.Std.uncurry_apply_pair`. This is why
  L036/L038/L043 failed: raw `rw` of ports under Aeneas `uncurry` tuple
  destructuring and against projection-shaped boundary heads. Uses the accepted
  NNV/NNX ports only (FinishCut/Tail, NativePorts.rounds/circle, FinishClaims,
  FinishTerminal, FinishRecord, FinishDecodePort, C1Gather/Mask10, ClaimPorts,
  LIB_VField exact lemmas, Masked.extra, Comparisons, FinishPayload, RootCopy).
- `NOC_Op9Slot.slot` (rfl): the op9 slot on `none` is `S1SemanticInstallation.verify`
  over `ClaimsUnrolledFinish.install (NP6_StdModel.calls r) (IDa_Deployed.boundaries r)`,
  `r = c.fixed.reservation`. `.digest` (rfl): retained host digest = `LIB_VCode.digest (envOf c)`.
  `.pub_round`, `.reservation` (from `(envOf c).reservation = true` via NNH_HostEnv.reserveOK_iff),
  `.prefix_finish`: full VerifyPrefix.verify Result from NNV_SemanticPrefix.returned + source.
- `NOC_Op9.op9` (L004): reservation derived from the SAME call (NNV_FinishClaims), then slot,
  verify unfolding, prefix_finish.

## X1 closed (1 scope, L005)

NNY's unrestricted NodeLeaf is false for LIBC on short openings (NNX_PartitionFinding),
so `NOC_MerkleBounded` restates the read-only NNY chain (rows, level, iterate, height,
endpoint, verify, terminal, active, loop, treeCode, tree, values, parent) with proof
bodies copied unchanged under a bounded companion `NOC_MerkleBounded.NodeLeaf D H`
(node law unrestricted; leaf law only for `opening.val.length = 832`, the width every
reached opening already proves). NNY sources are not edited; NNY's own `refDigest`,
`totalDigest`, `total`, `endpoint_total`, `slotBound` are reused by explicit open.
- `NOC_MerkleBounded.hostNode`: host checkpoint digest node law at `LIBC_CohortHash.H (envOf c)`
  (LIBC_HashShapes.node shape). `.host`: the bounded companion at
  `Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)`, leaf law from NNX_LeafAgreement.source.
- `.parent` (bounded, any `H D`, `k < 2`), `.hostParent` (host instance), and the exact
  k = 0 instance `.model0`: `LIBC_BatchMerkle.Domain a →
  NHT_ResultPort.action (LIBC_BatchMerkle.model a (envOf c)) = ok (.Ok ()) →
  Port4B_Install.batch (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)) (LIBC_Bytes.raw a.1)
  (LIBC_BatchMerkle.prepared a) (LIBC_BatchMerkle.folded a) 0#usize () = ok (.Ok ())`,
  via LIBC_BatchMerkle.source (not re-proved).
Not established here: that this digest and these arguments are exactly the op6 call of the
current 094 body (that is X7 bind-stepping).

## X4 stopped: the goal is false at the host configuration (3 scopes, L006-L008)

`NOC_PrepareDiv` (L008, standard axioms):
```lean
theorem op1_div {W Tx : Type} (c : Ctx W Tx) (n : Usize) (x : U8) :
 (DrvC_Installation.currentInstalled (configuration c)).op1 core.marker.CopyU8 n x = .div := rfl
theorem prepare_div {W Tx H : Type} (c : Ctx W Tx) (D) (pub) (proof : Slice U8) (hash : H) (obs) (g) :
 verifier.candidate.prepare (DrvC_Installation.currentInstalled (configuration c)) D pub proof hash obs g = .div
```
The installed 087 front begins `ops.op1 CopyU8 14759 0` (the `vec![0; n]` allocation,
library side `LIB_VLib.filledValue`). No installer in the host chain sets op1
(L006 prints: withValues, Tx1Q_PrefixInstall/Tx1Q_Install, BorrowedClaimPrepared.install
with ConcreteConstants.withConstants, NativeBuffers.install, S1SemanticInstallation; IDa
seed copies `missing.currentBase`, and NNH_HostSeed.m0.currentBase is `.div` in every slot).
So the prepare front diverges on every input, and the X4 statement (library prepare returns
ok ⇒ installed front returns the SAME Ok Prepared and scratch) is false at every input where
the library prepare returns ok. This is an instantiation gap in S_host's literal `missing`
record, not a proof difficulty. Details and the recommended repair are in NOC_REMAINING.md.
Per the brief I did not weaken the statement and stopped the job here (X2, X5-X9 not started).

## Overlay for G0 FINAL

`/home/dombarker/project-offloads/codex-cx-a1-20261108/NOC_objects` (hashes in NOC_OVERLAY.json),
prepended to the read-only NOC_PATHS.json list (NNX_objects, then NNX_PATHS.json unchanged).
Nothing was copied, moved, deleted or written in any cache or sibling overlay. Accepted roots
and printed axioms: NOC_ACCEPTED_ROOTS.json. NOC_PrepareInventory is diagnostic only (prints).
No delivered-type rfl example, raw ax2 walk or NOC_FinalCombined import exists, because there
is no field term. Stage commits on codex/cx-a1-20261107; no push.

target not yet established
