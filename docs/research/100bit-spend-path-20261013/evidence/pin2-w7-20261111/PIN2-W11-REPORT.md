# PIN2 W11 report (2026-11-11)

Scope: the host failures that followed the W7/W9/W10 restatements of the public input, and the
consumers behind them. These are the FJq/FJt public join, the FIz/FJk/FJn terminal chain, the
masked and endpoint compositions, and the NKR digest family. Worktree `fix/pin2-lean-20261110`.
Objects are in `overlay-PIN2-W7`. Compile ids run from PIN2W7_C0195 to C0421
(PIN2-W7-COMPILE.tsv), and every statement change is recorded in CHANGES.tsv.

## Validation

There were 227 local compiles. Each was one lean process (`-M7000`, `-DElab.async=false`),
with peak RSS 5.15 GB and longest wall time 26 s.

- **Batches 1–3** used the search path `overlay-PIN2-W7 : overlay-HOST-P1 : overlay-PIN2 : objs : base`
  (`PIN2W7_compile.sh`).
- **Batch 4** used `overlay-PIN2-W7 : overlay-HOST-P1 : overlay-PIN2-W4 : overlay-PIN2 : objs : base`
  (`PIN2W11_compile.sh`, a copy with only that path changed). This was the coordinator's
  instruction, so that the Mac fixture builds are used where the host has not reached.
- **Axioms:** the last compile of every credited module is exit 0. Its whole-log axiom check
  shows only `propext`, `Classical.choice` and `Quot.sound`, and no `sorry`.
- **Failed compiles:** 17 compiles were non-zero, and each was followed by a source change.
  - C0200, C0202 and C0207 were first attempts with a layout error, a missed function-level
    rewrite and a binder typo.
  - C0296–C0365 were NKR/NLH release texts failing on the public type change, and the
    over-retype described below.

  No failed compile was rerun unchanged. NKR_DigestWrapper and NKR_DigestComposed were
  recompiled from their release text only after the dependency that made them fail had been
  reverted.

## Release identity (method and counts)

Each original was taken from git. A module with several candidate blobs had each candidate
tried in order, as W3c did. Every original was compiled against `objs : base` before any edit
and its object compared with `objs`. A candidate was accepted if its object was byte-identical
or differed only in the embedded source-path strings (PATHONLY: the only differing strings end
in `.lean`).

| Set | Modules | Identical | Path-only | Log |
|---|---|---|---|---|
| Batches 1–3 | 81 | 77 | 4 | logs/identity/W11-IDENTITY.txt |
| Batch 4 (NKR + NLH) | 72 | 62 | 10 | logs/identity/W11-NKR-IDENTITY.tsv |

In batch 4, 24 NKR modules and 4 NLH modules had several candidates. The rejected candidates
are logged (24 FAIL, which did not compile against objs, and 1 DIFFERENT for NLH_SemanticState).
Every module has exactly one accepted blob.

## Batches

| Batch | Commit | Host order | Contents |
|---|---|---|---|
| 1 | 97ddf2fce08 | HOST-ORDER-W11.tsv | host failures FJt_PrepareHead, FJa_PublicOnPreparation, FIz_SameComposition; FJq/FJt public chain; new PIN2W11_PublicCopy |
| 2 | 16c90435e36 | HOST-ORDER-W11-2.tsv (replaces rows 1–11 of batch 1) | approved import narrowing of RPv_FJq_PublicField; FJq chain rebuilt on it |
| 3 | c5bcebd2c0d | HOST-ORDER-W11-3.tsv (68 modules) | host failure FJk_SemanticWideOnRun; FJk/FJn terminal chain, masked and endpoint modules on nativePIN2 |
| 4 | ea67aae5b2f | HOST-ORDER-W11-4.tsv (73 modules) | NKR digest family on the PIN2P route, new PIN2W11_DropCoe, NLH users |

## Classes of change

### New modules

- **`PIN2W11_PublicCopy`** defines `nativePIN2 q`, the release `FJa_PublicCopy.native q` plus the
  PIN2 `destination` field. That field is `none` for a transfer and `some destination_token_account`
  for a withdrawal, as the Rust `private_public` / `withdrawal_public` set it at c7593d23fdc.
  - It also proves `drop`: `(nativePIN2 q).dropDestination = native q`, by rfl. This ties it to
    the extracted pre-PIN2 constructor on the nine old fields.
  - It also proves `byte_eq` / `bytes32_eq`: the probe helper byte equals `RawBridge431.rawByte`.
  - Provenance: the probe emission contains only the struct, so there is no PIN2 `on_statement`.
    `nativePIN2` is a named value, not an extraction claim.
- **`PIN2W11_DropCoe`** is a scoped coercion from the PIN2 public to the pre-PIN2 native struct by
  `dropDestination`, in that direction only.
  - The coordinator accepted it as a notation device: every elaborated term is
    `PIN2P.SemanticPublic.dropDestination p`.
  - No coercion promotes a native public to a PIN2 one.

### Conclusion unchanged; premises retargeted to the PIN2 transcript or bytes (W7 pattern)

The premise becomes the PIN2 `public_transcript` of `PreparationBinding.toPIN2 …`, with
`D` and `t0`/`out` carried by `PIN2W7_TranscriptCopy`. Their binder types stay frozen.

- RPv_FJa_PublicOnPreparation
- RPx_FJt_AcceptedMaskedLiteral and RPx_FJt_Endpoint (only the `publicSame` premise moves to
  `nativePIN2`)
- RPv_FJk_SemanticWideOnRun (`bounds` and `run` on `p.dropDestination`)

### Serializer conjunct retargeted to the PIN2 bytes

- RPv_FJt_PrepareHead, a cascade from W9's `F3U_PrepareHead`
- RPv_FJt_PublicLog
- RPv_FJq_PublicOnPreparation, whose serializer conjunct is now on `toSerializer s`, the PIN2
  carrier since W3c
- RPv_FJt_PublicJoin, whose `serialized` premise changes

In each case the head, `pubBytes`, `parsePublic` and frozen `SemanticTranscript.new` conjuncts
are textually unchanged.

### Public-model side moved from `native` to `nativePIN2`

W3c retyped `FIw_PublicModel.ofPublic` to the PIN2 struct, so the release text no longer
typechecks. The coordinator decided that the terminal chain is stated on `nativePIN2`, with the
destination included. These modules change:

- RPv_FJq_PublicNative, RPv_FJq_PublicWire and RPv_FJq_SourceLiteralPublic
- RPv_FJq_PublicOnPreparation and RPv_FJt_PublicJoin (their model conjuncts)
- RPv_FJn_NativeTerminal and RPv_FJn_MainTerminal (the `terminalValue` public argument)
- RPx_FJq_MaskedMain, RPx_FJq_MaskedLiteral and RPx_FJt_AcceptedMaskedMain (the `terminalZ` public
  argument)

The native `Bounds (FJa_PublicCopy.native X)` premises are unchanged.

### Carrier change: the public binder is the PIN2 struct and native reads go through `.dropDestination`

The conclusion text is unchanged unless noted.

- RPv_FIz_SameComposition: the `semantic_packed` conjunct now reads `p.dropDestination`.
- RPv_FJk_CompositionWideOnRun, RPv_FJn_CompositionCopyOnRun, RPv_FJn_CompositionModel and
  RPv_FJn_TerminalModel.
- RPv_FJn_TerminalPartsValue: the `composition pub` conjunct becomes
  `composition pub.dropDestination`.
- NKR, where the statement names `ofPublic`:
  - NKR_DigestOldPack.source
  - NKR_DigestKeyValues
  - NKR_DigestFrontierSum
  - NKR_DigestOptionalValue
  - NKR_DigestAssociation
  - NKR_TermSemanticModel.source (NKR_TermSemanticModel.bounds keeps its native binder)

### Proof only

- **RPv_FJn_CompositionActive** applies the restated lemma at `PIN2P.SemanticPublic.embed p`.
- **NKR_DigestRoot** instantiates `NKR_DigestOldPack.source` / `NKR_DigestAssociation.model`
  at `embed p`. Coordinator ruling, recorded in CHANGES.tsv: "The proof-internal
  instantiation at embed p in NKR_DigestRoot is acceptable: the statement is native and
  untouched, and the model-side terms cancel inside the proof, so the "not embed p" rule
  (which is about statements and boundary values) is not touched."

### Import only

**RPv_FJq_PublicField** (coordinator-approved): `RPv_FJn_MainTerminal`, from which nothing was
used, is replaced by `RPv_FIz_ConcretePack` and `R1ExactBaseProjection`. Statement and proof
are unchanged.

### W3a text plus a layout fix

**RPv_FJq_PublicModel**: W3a's continuation line for the withdrawal `destination` field did not
parse (C0200). It was joined onto the previous line, with no other change.

### Rebuilt unchanged

- RPv_FJt_DecodedPublic, RPv_FIz_Audit and RPx_FJt_RunEndpoint. RunEndpoint's inputs line up with
  the restated PublicLog/PublicJoin/Endpoint and W7's F3M/init-call forms.
- 54 further terminal-cone modules (HOST-ORDER-W11-3).
- 53 NKR modules and all 12 NLH modules (HOST-ORDER-W11-4).

## The digest family keeps its meaning

R0P.digestKeys, digestRow, digestStart, digestTarget and publicDigestLanes read none of pool,
deploymentDomain or destination.

- `R0P/Digest.lean` at PIN2 is textually identical to the pre-PIN2 v8 file.
- `FIz_PublicDigest` equates the native model on `p.dropDestination` with those lanes.
- The Rust `public_digest_lanes` (pair_forest_semantic_terminal.rs:626) is untouched by
  4bb3b3f..c7593d23fdc.

The binding fields enter the proof only through the `public_bytes` serialization, and so
through the transcript. Every NKR digest statement change is therefore a carrier change, with
its text and meaning unchanged.

## Reverted over-retype (batch 4)

The first automatic NKR pass retyped every module that failed on the PIN2 type.

- **What was retyped:** NKR_DigestRoot, NKR_DigestWrapper and NKR_DigestComposed, whose statements
  are purely native, and then NLH_SemanticState, NLH_DigestWrites and NLH_DigestChain.
- **Why it was wrong:** this changed the type of the native NLH step function
  (`NLH_SemanticState.step`), and NLH_ScalarChain failed (C0365).
- **What replaced it:**
  - All six modules were reverted. Their sources are in `quarantine/W11-overretype/` (moved,
    not deleted).
  - NKR_DigestRoot became a proof-only change.
  - NKR_DigestWrapper, NKR_DigestComposed and the 12 NLH modules now compile from unchanged
    release text.
  - NKR_TermSemanticModel.bounds was given back its native binder.
- **Rule applied afterwards:** a module is retyped only when its statement names `ofPublic`, a
  model object, or a def that does. None of the reverted versions was committed or put in a
  host order.

## What remains provisional

- **Not a coherent replay.** Every local pass compiled against host objects where they existed
  and against `objs` (or the W4 fixture objects) everywhere else.
  - The roughly 1,060 unbuilt modules upstream of NKR were not rebuilt locally (NF* … NKJ*,
    RPx_Deployed, the RPx_FJv_D* modules, the COMBINED_IMPORT modules).
  - Neither were the modules downstream of the restated ones beyond those listed.
  - The host replay must rebuild them, and any declaration-level link that this audit missed
    will appear there as a compile failure.
- **Provenance.** `nativePIN2` and the PIN2 `SemanticPublic` struct come from the probe crate
  (HM-D at best). There is no extraction of the PIN2 semantic-public constructor itself.
- **Not yet done.** The final-closure axioms audit, the two top theorems on the host, and the
  release-artifact binding are still outstanding. The release target is unchanged: these are
  model and proof restatements at the PIN2 pin.

Target not yet established.
