# PIN2 W10 report (2026-11-11)

Scope: the instrumented NNV family, NOC_Op9Slot / NOC_Op9 / NOC_SemConv, the rest of the
instrumented family in NSTAR-VERIFY-USERS.tsv, and the 22-module watch list of users of
`S1SemanticInstallation.verify`. Worktree `fix/pin2-lean-20261110`. Objects are in
`overlay-PIN2-W7`. Compile ids run from PIN2W7_C0130 to C0194 (PIN2-W7-COMPILE.tsv); all
statement changes are in CHANGES.tsv.

Every local compile ran as one lean process (`-M7000`, peak RSS at most 5.61 GB). Each
whole-log axiom check found only `propext`, `Classical.choice` and `Quot.sound`, and no
`sorry`. There were two failed compiles. C0135 (NOC_Op9Slot) failed on a syntactic
`VL.c1Root` / `LIB_VCarriers.c1Root` mismatch in a `rw`; the source was changed and C0136
passed. C0128 belongs to W9.

## Release identity

All 64 release originals used by W10 were rebuilt against `objs:base` before any edit
(logs/identity/W10-*.log, W10-IDENTITY.txt). Each object was either byte-identical to objs
or differed only in the embedded source-path string.

## Why the change reached the observed library

The top statement (`TAS_FinalB.deployed_splitB`) names `NNH_Libraries.VL`. The
public-transcript child of that library is `LIB_VPublicTranscript.code`, which was defined
on the frozen serializer (`NHG_PublicTranscript.packetCode`). Unless that definition
changes, the observed library still models the frozen verifier. Then `NOC_Op9.op9` (the
installed PIN2 verify equals the observed library value) cannot be restated with its
conclusion unchanged.

The coordinator approved two definition changes: `LIB_VPublicTranscript.code` and the
matching `NMP_Install131.publicTranscript`. The rest of this report follows from those two
changes.

## Changes by class

### Definition changes

| Module | Change | Approval |
|---|---|---|
| `LIB_VPublicTranscript` | `code a env := S1SemanticCode.publicTranscriptPIN2 (LIB_VCode.digest env) a.1 () (LIB_Env.nativeKey a.2)` | coordinator-approved |
| `NMP_Install131` | `publicTranscript := outer (inner fromT10 fromT12) (erase (publicTranscriptPIN2 (digest d) (toT9 p) hash root))` | coordinator-approved |
| `NNG_Events137` | in `events`, the `TX1:131/public_transcript` arm now emits the library events of `publicTranscriptPIN2` | forced consequence of the two approved changes; recorded by the coordinator |

### Statement changes (conclusion or premise text)

| Module | What changed |
|---|---|
| `LIB_VPublicTranscript` | `source` (now `rfl`) and `law_exact` name `publicTranscriptPIN2`. |
| `NNV_SemanticTranscript` | `source` RHS is `rmap (cres transcriptBack errorBack) (PIN2 public_transcript (TranscriptCopy.digest D) (toPIN2 a.1) () key)`. `returned` concludes the PIN2-on-copies form `... = .ok (.Ok (TranscriptCopy.transcript t))`. Premise unchanged. |
| `NNV_SemanticPrefix.returned` | Only the initialized conjunct changes, to the PIN2-on-copies form. |
| `NOC_ConvSemantic.transcript` | Only premise `h` changes, to the PIN2-on-copies form. The conclusion is unchanged. |
| `NOC_Op9Slot.prefix_finish` | Coordinator-approved. The LHS is `NJG_ObservedInstall.prefixPIN2` with the same arguments and frozen carriers. The conclusion value `.ok (.Ok (LIBC_PreparedCarriers.verified LIB_Prepared.types sem))` is unchanged. |
| `NMP_Install131` | `same` and `source` RHS now give the PIN2 transcript. `source` has no consumer. |
| `NNG_PublicSource137.value`, `NNG_PublicProjection137.projected` | The RHS names `publicTranscriptPIN2`. |
| `NNG_Events137.public_call` | Restated to match `events`. |

### Proof-only changes (statements unchanged)

- `LIB_VPublicAsset.code_asset` is now proved from success of the PIN2 serializer:
  `publicTranscriptPIN2_erasure`, then `TranscriptCopy.public_transcript_split`, then W3c
  `PIN2Whole.source_success`.
- `NOC_Op9.op9` and `NOC_SemConv.op9` now rewrite with the new `NOC_Op9Slot.installed_verify`.
  `NOC_SemConv.op9` also uses the new helper `ptInv` and unfolds `prefixPIN2`.
  `NOC_SemConv.finish` is unchanged.
- `NNG_StageValues137` and `NNG_Occurrences137`.
- `NNQ_PreparePort`: the private `semantic_dictionary` now uses
  `verifyPIN2_dictionary_irrelevant`.

Conclusions kept: `NOC_Op9.op9`, `NOC_SemConv.op9` / `finish`, `LIB_VPublicAsset.code_asset`,
every `NOC_ConvSemantic` conclusion, and the `NOC_Op9Slot.prefix_finish` value.

### New declarations and twins

- `NOC_Op9Slot.installed_verify`: `S1SemanticInstallation.verify` equals the release body
  with `prefixPIN2`, via `S1SemanticCodeInstallation.source` and `prefixPIN2_erasure`.
- `LIB_VPublicAsset.asset_step_PIN2` and `bytes_asset_PIN2`.
- `NOC_SemConv.ptInv`.
- New module `PIN2_NNQ_SemanticPort`: PIN2 versions of the dictionary-irrelevance lemmas
  (they show the code does not depend on which digest implementation it is given) for the
  PIN2 `newTranscript` / `publicTranscript`, `publicTranscriptPIN2` and `verifyPIN2`, plus
  the PIN2 error-closure facts. The release `NNQ_SemanticPort` is unchanged.

### Audits (source unchanged, compiled unchanged on the W10 overlay)

- **Instrumented family closed by audit.** `NLJ_ObservedDirect`, `NLJ_ObservedDenote`,
  `NLJ_ObservedInitial`, `NLJ_ObservedStep`, `NLJ_ObservedWindows`,
  `NLJ_Run_publicTranscript`, `NKQ_ObservedTrace`, `NNQ_SemanticPort`,
  `NHG_FrontComposition` and `NHG_PublicTranscript` (plus `NLJ_Run_parse`) state facts about
  the frozen lifted code, and those facts are still true. None of them unfolds a changed
  definition, and no release-closure declaration links them to one:
  - NLJ is used only inside NLJ.
  - `NMP_TransportBase` and `NNG_TransportBase` import `NLJ_ObservedInitial` without using it.
  - `NKQ_ObservedTrace` and `NHG_FrontComposition` have no closure user.
- **Byte-length literals.** None of 1455, 1427, 1520 or 1524 occurs in these modules or in
  any module W10 touched, so no literal was changed.
- **Rebuilt unchanged against the restated modules:** `LIB_VParse`, `LIB_VDomains`,
  `NNG_PublicErasure137`, `NNG_Data137`, `NNG_Caller136From137`, `NNG_Context137`,
  `NNG_ReturnedPath137`, `NNG_SourceBegin137`, `NNG_SourcePublic137`, `NNG_Events087`,
  `NNG_FinishOccurrence137`, `NNG_Head137`, `NNG_Producer137`, `NNG_SourceParse137` and
  `NNQ_FirstCode`.
- **Watch list (22 modules), all compile unchanged.**

  | Object vs objs | Modules |
  |---|---|
  | Identical (14) | `RPz7_S1NativePrepareBuffersV1`, `RPz7_S1OwnedStage1NumericV1`, `RPz7_S1PrepareNumericV1`, `RPz7_PAln_BothBuffers`, `RPz7_PAln_OpeningReach`, `RPz7_SAP_Cuts`, `RPz7_F3P_SemanticClaims`, `RPz7_F3P_SemanticY`, `RPz7_SAP_OpeningCuts`, `RPz7_F3P_Prepared`, `RPv_FIr_AlphaCanonical`, `RPv_FJa_NativePoint`, `RPv_FJt_AlphaOnRun`, `RPv_FJa_ReadersOnRun` |
  | Path-only difference (4) | `RPz7_S1NativeBufferClaimTraceV1`, `RPz7_S1NativeBufferPreparedTraceV1`, `RPz7_F3P_SemanticClaimsY`, `RPu_FIq_TypedData` |
  | Structural difference (4) | `RPz7_SAP_SemanticCanonical`, `RPz7_SAP_SemanticCircles`, `RPu_FIq_SemanticSource`, `RPx_FIr_AcceptedTerminal` |

  In the 4 structural cases the object mentions the PIN2 names because these modules
  destructure the restated `verify_roots` / `F3M_SemanticSource` statements. They do not use
  the public-init conjunct.

## Host orders

| File | Rows | Contents | Commit |
|---|---|---|---|
| HOST-ORDER-W10-1.tsv | 11 | LIB / NNV / NOC chain | a4f1f81db9c |
| HOST-ORDER-W10-2.tsv | 12 | NMP_Install131 and the NNG 137 family | a73e05dd2d8 |
| HOST-ORDER-W10-3.tsv | 2 | PIN2_NNQ_SemanticPort, NNQ_PreparePort | c8834803793 |
| HOST-ORDER-W10-4.tsv | 22 | watch list, all unchanged sources; olean hashes are for cross-checking | this commit |

## What remains provisional on the host

- Every local pass was compiled against `overlay-PIN2-W7 : overlay-HOST-P1 : overlay-PIN2 : objs : base`.
- The modules between the changed definitions and the restated consumers were not rebuilt
  locally; W10 compiled against their pre-change objects. Examples are `LIB_VLib`,
  `NNH_ObservedReturns`, `NNV_ObservedCut`, the `NNH_Run5b*` chain, `NNQ_COMBINED_IMPORT`
  and the other NNG/NMP modules. That cone (about 700 modules downstream of
  `LIB_VPublicTranscript` and about 200 downstream of `NMP_Install131`) must be rebuilt by
  the host. A W10 local pass is not a coherent replay.
- Some `overlay-HOST-P1` objects were stale while the host was rebuilding. Example:
  `NKQ_ObservedTrace` rebuilt unchanged to an object that differs from objs by 160 bytes with
  no differing strings, presumably because of host-built frozen `RPz7_S1SemanticCode*`
  dependencies.
- The closure-use audits rest on a text search of the latest git sources plus the release
  import graph (`pin2-public-binding-20261110/impact-scan/imports.tsv`). Any declaration-level
  link they missed would show up as a host compile failure, not as a silent inconsistency.
  The exception is a frozen-code fact joined to the deployed program by some route other
  than the changed definitions; the audit found none.
- The release target is unchanged. These are model and proof restatements at the PIN2 pin.
  The coherent replay, the axioms audit of the final closure and the artifact binding are
  still outstanding.

Target not yet established.
