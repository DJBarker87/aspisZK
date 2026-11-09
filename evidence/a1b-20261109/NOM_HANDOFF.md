# NOM handoff: terminal domain (T) and reverse batch Merkle (M)

Target not yet established. Both commissioned model lemmas are proved; neither is an A1 field term.

Scopes: 7 of 28 (6 pass, 1 fail); 0 Kani, 0 extraction. Caps as NNX/NOC (MemoryHigh 6G, MemoryMax 8G,
MemorySwapMax 0, TasksMax 64, `lake env lean -j1 -M7000 -DElab.async=false`, 180 s), admission allowed:true,
whole-host lean count < 6 and disk >= 40 GB at every launch. Per-scope target, exit, wall, peak RSS, swap,
revision and printed axioms: NOM_COMPILE.tsv (peak RSS 6.79-6.84 GB, swap 0, wall 26-28 s). Client NOM_run.py
(NOC_run.py with prefix NOM, budget 28, own host directory). No cap, heartbeat, timeout or recursion limit raised.
No sorry, axiom or native_decide in any accepted module. Every printed root is standard (propext, Classical.choice,
Quot.sound). L002 failed only on statement elaboration (`.ok 0#usize` against a pure Usize `%`; the proof never ran);
L003 writes `ok 0#usize` as F3Q_VerifyGuards does and passes.

## (T) terminal domain: closed, no counterexample (L001, module NOM_TerminalDomain)

The digest half is exported by the frozen validator: NMT_345.validated_public_domain (CLOSED276) already proves
NKR_DigestChildren.Domain of the validated statement's semantic public, and LIB_S1.validated_public restates it
for the library C. The new step is that the installed op21 Ok is that validator's Ok at the SAME carrier.

```lean
theorem AspisR1.NOM_TerminalDomain.validate_native (st : NNH_S1HostCodec.Statement)
 (good : NNH_S1HostCodec.validate st = .ok (.Ok ())) :
 NMT_345.validateCall (NNH_S1DecodeOk.carrier st) = .ok (.Ok ())
theorem AspisR1.NOM_TerminalDomain.validate_iff (st) :
 NNH_S1HostCodec.validate st = .ok (.Ok ()) ↔ NMT_345.validateCall (NNH_S1DecodeOk.carrier st) = .ok (.Ok ())
theorem AspisR1.NOM_TerminalDomain.validated_digest (st : NNH_S1HostCodec.Statement)
 (good : NNH_S1HostCodec.validate st = .ok (.Ok ())) :
 LIB_VPublicDomain.publicDigestDom (NNH_Libraries.C.semanticPublic (NNH_S1DecodeOk.carrier st))
theorem AspisR1.NOM_TerminalDomain.library_digest (st : NNH_Libraries.C.Statement)
 (good : NNH_Libraries.C.validateStatement st = true) :
 LIB_VPublicDomain.publicDigestDom (NNH_Libraries.C.semanticPublic st)
theorem AspisR1.NOM_TerminalDomain.asset (pub : LIB_VCarriers.Public) (r : RSL.B32) (env : RSL.Env) (t : Transcript)
 (returned : LIB_VLib.publicTranscriptValue (pub,r) env = .ok t) : LIB_VPublicDomain.publicAssetDom pub
theorem AspisR1.NOM_TerminalDomain.domain (a : LIB_VTerminal.Args) (r) (env) (t)
 (digest : LIB_VPublicDomain.publicDigestDom a.1)
 (returned : LIB_VLib.publicTranscriptValue (a.1,r) env = .ok t) : LIB_VTerminal.Domain a
theorem AspisR1.NOM_TerminalDomain.reached (st : NNH_S1HostCodec.Statement)
 (good : NNH_S1HostCodec.validate st = .ok (.Ok ())) (a : LIB_VTerminal.Args)
 (same : a.1 = NNH_Libraries.C.semanticPublic (NNH_S1DecodeOk.carrier st)) (r) (env) (t)
 (returned : LIB_VLib.publicTranscriptValue (a.1,r) env = .ok t) : LIB_VTerminal.Domain a
theorem AspisR1.NOM_TerminalDomain.terminal (a : LIB_VTerminal.Args) (env : RSL.Env) (dom : LIB_VTerminal.Domain a)
 (raw : LIB_VScalarCarriers.RawQ)
 (h : FIq_Terminal.terminal a.1 (claimsRaw a.2.1) (alphaRaw a.2.2.1) (challengesRaw a.2.2.2) = .ok (.Ok raw)) :
 ∃ q, LIB_VLib.terminalQm31Value a env = .ok q ∧ LIB_VScalarCarriers.toRaw q = raw
```
`terminal` is the terminal converse port (the open "terminal" row of NOC's converse table) on the Domain, which
`reached` supplies on the 345 path from op21 Ok plus the returned public transcript. Because the domain holds
whenever op21 accepts, there is no reached input where the native terminal is Ok off publicDom: no weak-Err
counterexample exists on this path.

What `reached` does not do (left to NOC's X8 composition, not a model lemma): prove that the public the model 345
body passes on (`PoolV1PairForestTerminalStatementV1.semantic_public val2`, then FirstComposition.toCurrentPublic)
is the image of `NNH_Libraries.C.semanticPublic (NNH_S1DecodeOk.carrier val2)`. I also did not re-check by rfl
that the S_host sdk op21 is `NNH_S1HostCodec.validate` (NOC's table lists NNH_S1HostCodec as the 345 codec port).

## (M) reverse batch Merkle: closed (L003-L006)

Leaf-first converse of the NNY/NOC_MerkleBounded chain, under the SAME bounded companion
`NOC_MerkleBounded.NodeLeaf D H` (832-byte leaf law), and the SAME domain hypotheses as the forward parent
(`k.val < 2`, canonical queries). No hash injectivity, Root0, success, representation or selector premise;
the adversary is universal (every proof/prepared/folded input).

- `NOM_MerkleGuard.scan` (new): inversion of the extracted `reference.valid_indices` (canonical indices, strictly
  ascending adjacent pairs). `.well`: the owned verifier's guards give `OraclePortFrozenOrder.wellFormed` of the live
  indices (converse of NNU_MerkleHead.source). `.aligned`, `.guards`: everything an accepted `verify_owned` exposes
  at any digest instance (well-formed, aligned, levels Done, root guard).
- `NOM_MerkleVerify.endpoint`: `reference.verify_owned (refDigest D) () root s physical = .ok (true,out)` ⇒
  `(eval H (MultiproofConeVerifyState.verifyState root physical s)).2 = (true,out)` (s.at = 0), via `.guards`,
  NOC_MerkleBounded.height (an equality) and the eighteen-level transport equality. `.verify`: installed P6 verify
  Ok ⇒ `NKV_ConcreteChildren.verify` Ok with the SAME outputs.
- `NOM_MerkleLoop.terminal` (every tail read is an equality except verify), `.loop` (NNY_LoopTransport.accepted with
  the dictionaries exchanged; `active` is the equality).
- `NOM_MerkleParent.treeCode`, `.tree`, `.values`, then:

```lean
theorem AspisR1.NOM_MerkleParent.parent (H : Bytes → AspisV8R19.SourceDuplexStep.State)
 (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (agree : NOC_MerkleBounded.NodeLeaf D H)
 (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (folded : Array U8 32#usize)
 (k : Usize) (hk : k.val<2) (q : ∀ j,j<22 → p.queries.val[j]!.val<262144)
 (accepted : Port4B_Install.batch D proof p folded k ()=ok (.Ok ())) :
 NHT_ResultPort.action (NKV_FRef.verifier.candidate.batch_merkle
  (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H) proof p folded k ())=ok (.Ok ())
theorem AspisR1.NOM_MerkleParent.parent_iff (H D agree proof p folded k hk q) :
 NHT_ResultPort.action (NKV_FRef...batch_merkle (ops H) (digest H) proof p folded k ())=ok (.Ok ()) ↔
 Port4B_Install.batch D proof p folded k ()=ok (.Ok ())
theorem AspisR1.NOM_MerkleParent.hostParent {W Tx} (c : NNH_Run5bCtx.Ctx W Tx) proof p folded k hk q
 (accepted : Port4B_Install.batch (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)) proof p folded k ()=ok (.Ok ())) :
 NHT_ResultPort.action (NKV_FRef...batch_merkle (ops (LIBC_CohortHash.H (envOf c))) (digest (LIBC_CohortHash.H (envOf c)))
  proof p folded k ())=ok (.Ok ())
theorem AspisR1.NOM_MerkleParent.model0 {W Tx} (c : NNH_Run5bCtx.Ctx W Tx) (a : LIBC_BatchMerkle.Args)
 (domain : LIBC_BatchMerkle.Domain a)
 (accepted : Port4B_Install.batch (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)) (LIBC_Bytes.raw a.1)
  (LIBC_BatchMerkle.prepared a) (LIBC_BatchMerkle.folded a) 0#usize ()=ok (.Ok ())) :
 NHT_ResultPort.action (LIBC_BatchMerkle.model a (envOf c))=ok (.Ok ())
theorem AspisR1.NOM_MerkleParent.model0_iff (c a domain) :
 NHT_ResultPort.action (LIBC_BatchMerkle.model a (envOf c))=ok (.Ok ()) ↔ Port4B_Install.batch ... 0#usize ()=ok (.Ok ())
```
`parent` at k = 0 is NOC's open goal 2 verbatim with the forward parent's hypotheses; `model0`/`model0_iff` are
the exact converse and Ok-iff of NOC_MerkleBounded.model0 (the host companion is discharged by
NOC_MerkleBounded.host c, so no agreement premise remains). `envOf` is NNH_Run5bCtx.envOf, as in model0.

## Combined import (L007)
`NOM_FinalCombined` imports the five NOM modules and the thirteen NOC modules with printed roots
(NOC_FinishSource, Op9Slot, Op9, MerkleBounded, PrepareDiv, Run5bHost, PrepareFront, ReadTransport, QueryLink,
QueryDomain, ConvLeaves, ConvSemantic, Conv094) in one scope, typechecks three `example`s at the delivered (M) and
(T) types, and prints axioms of all 25 NOM roots and 92 NOC roots: standard only (one NOC root,
NOC_PrepareFront.window, uses propext and Quot.sound only). Accepted roots: NOM_ACCEPTED_ROOTS.json.

## Overlay
`/home/dombarker/project-offloads/codex-cx-a1b-20261109/NOM_objects` (hashes in NOM_OVERLAY.json), prepended to
NOM_PATHS.json = [codex-cx-a1-20261108/NOC_objects] + NOC_PATHS.json. Stage commits on codex/cx-a1b-20261109; no push.

target not yet established
