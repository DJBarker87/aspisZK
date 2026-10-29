# PV_DIAG7 — D458: adopted option B for diagnostic environment outcomes

**Target not yet established.** Worktree `/Users/dominic/ZK/.worktrees/pv-diag`, branch `codex/pv-diag7-20261029`, base `444380cd27`. The adopted public-input diagnostic model and its conditional decoder-facing law are checked. The universal deployed-client instance is not established.

## Adopted condition and exact theorem

D215 / ledger **V400** is the single shared option-B P row: the reached environment-failure event must be witness-independent. The environment signal is public to **both** experiments; the complete observer and existing error bound remain. No `OsAvailable` trust item, quiet-error convention, fixed-success schedule, empty-error schedule or new simulator is introduced.

The named public-input theorem is **`PV_DIAG7.DIAG_optionB_public_signal`**, in `PV_DIAG7_Audit.lean`, accepted by 65797. For every public program family `program : P → C → Nat → Program`, public initial diagnostic state, existing L1 public count, and public signal `P → C → Signal`, equal public data and the same original public coin coordinate give equality of the **whole function** of finite prefix coordinates:

```
(count, ordered diagnostic events, retained diagnostic state, terminal, ordered calls)
```

The signal includes typed write counts/errors/Interrupted flags, flush and file errors, reservation success bits, errno, strerror bytes, environment values and logger/backtrace/capture configuration. Requests, operands and continuations are separate public data. Every OS result remains a variable; errors and partial delivery are retained. Both experiments receive the same signal and same diagnostic transducer. This is a deterministic fixed-public-input result; the native selection/transport of that input still requires V400.

`DIAG_public_given_optionB` is the general same-coordinate form. Its `V400_OptionB_P` is an explicitly **sufficient source criterion**, equality of the complete selected signals on the same public/coin coordinates. It is stronger than equality of a Boolean failure event, and is **not** a new definition or a proved instance of ledger V400. The public-input specialization discharges that criterion by construction; it does not require adding it to the endpoint. The model lemmas `equal_failure_bit_not_equal_content` and `failure_bit_agrees_for_distinct_errors` exhibit distinct errno values with the same failure bit. They are specification checks, not a shipped-client leak. No independence of an endogenous signal mixture is inferred from the fixed-signal result.

`DIAG_native_handoff` states the additional native requirement openly: complete native events/state/terminal must equal the public program execution **before** applying the decoder. This `sourceBinding` is not discharged. Publicizing OS replies cannot prove that witness-bearing operands, request occurrence or call order are public.

## What the checked models cover

`PV_DIAG7_Effects` proves environmental write/flush/file/error/configuration dataflow. `PV_DIAG7_Program` permits adaptive continuations on every reply, retaining invocation order and all emitted prefixes of its finite programs. It does not replace an infinite execution by finite fuel exhaustion. Its programs finish normally; their errors are returned values. Actual abnormal executions require separate association.

`PV_DIAG7_Write` instantiates the **existing** `PV_DIAG3.writeAllStep/writePrefix`, preserving partial writes, zero writes, Interrupted guard/destruction, non-Interrupted return, bounds checking, and the supplied actual suffix. `optionB_every_write_prefix` covers all finite write-prefix coordinates jointly. Abort/divergence/panic in the supplied suffix are retained; neither their native identity nor public payload is inferred.

The nonce model preserves successful reservation **true or false**, reset of `last_error` to None, and failure-kind retention. `nonce_last_error_kind` does not expose the nonce-derived path or written nonce/digest as public data. Generic successful file-read contents are excluded. `print_to_message_public` proves only the selected public label/error-renderer message; it is not a law for the complete panic hook. The lossy renderer is an arbitrary public pure conversion, with its native UTF-8 representation association retained.

`optionB_bound_unchanged` is equality transport of an already supplied complete-observer bound, with the **identical epsilon**. It is not a new cryptographic bound or a proof of a bound for an endogenous environment mixture. The existing checked option-B fixed-signal theorem `R1Z.PV_RunJoin_PublicFailureOption.bound_unchanged` is read and reused as context, without replay or source edits.

## Native source association and boundaries

`source-bindings.json` rechecks **17 exact deployed source regions**, with file/body hashes and ordered checks, plus the inherited deployed build-unit feature inventory: rustc 1.94.1; `devnet_spend`; `r1p-check,aspis-r1-cost-probe/ct-host-prover`; release opt-level 3, debug assertions/overflow checks off, panic unwind. No artifact was rebuilt and no new runtime or singleton-domain evidence is claimed.

This is **own-1 environmental-input dataflow association, incomplete whole native binding**. The error-to-signal equations are model equations, not an independent source-to-code proof. V370 and pending D381/D386 remain. Native syscall/errno representation, permitted write-count range, borrow/store/drop glue, mutable logger/TLS/lock state and full capture/formatter execution are retained obligations.

The nonce source bytes match the inherited deployed SHA `4f6967771c5b7aaaebbd2967c6db1561e2d69de6c4c0f06f8d48a90f6d7ac2f7`. Its path depends on `mask_nonce`; it writes `statement_digest` and `mask_nonce`. Those are **not environment outcomes**. Relating the reached file-fault history to V400 must retain V337/V338's same-history and byte-blindness obligations. No nonce file or account/key state was created, opened, reserved or modified.

## Complete sink disposition

“Conditional public-only” below is a checked model law for public operands, initial state and invocation program, under the adopted public-input interpretation. It does not assert the missing whole-client native instance. Every environmental portion refers to the **same D215 / V400**, never a separate trust item.

| Sink / precursor | Disposition and remaining obligation |
|---|---|
| Successful main stdout JSON, account/count/audit/protocol/timing | **UNRESOLVED** whole public joint serialization/invocation law. fd1 delivery/failure is **conditional public-only** under V400 (`fd1_public`, write-prefix laws). V394 count disclosure and existing D163 count law reused. |
| Final Rejected report/tag | **NOT REACHED**, inherited scoped retry Result association/RejectFree; earlier attempt effects survive. |
| Local semantic/mask mapper and direct retry-controller diagnostics | **NOT REACHED locally**, inherited scoped binding; callbacks/body/drop/timing remain **UNRESOLVED**. |
| Eleven selected unit prover-error spellings / exhaustion text | **REACHED, selected content public-only**, inherited conditional law. Honest variant and invocation law remain **UNRESOLVED**; environmental delivery is conditional under V400. |
| Report after successful main Result | **NOT REACHED in that arm**, inherited theorem; no universal-success claim. |
| plan::err → anyhow → Termination → stderr / returned API suffix | OS error data, public error renderers and fd2 delivery **conditional public-only**, V400 (`returned_error_public`, `DIAG_optionB_public_signal`). Non-OS operand, occurrence, formatter/capture/drop/unwind and native association remain **UNRESOLVED**. |
| Client ensure/anyhow guards, non-prover/preparation errors, fancy ensure operands | **UNRESOLVED** guard exclusion or public selected operands/lengths. OS error status alone does not discharge them. |
| Nonce-store returned errors / last_error | Status, reservation Boolean, reset and error-kind retention **conditional public-only**, V400 (`nonce_failure_retained`, `nonce_success_resets_error`, `nonce_last_error_kind`). Native reservation-path, nonce/digest request history, E2 and V337/V338 association **UNRESOLVED**. |
| fd1/fd2 write, partial delivery, outer flush failure, Interrupted retry | **Conditional public-only**, V400 (`write_success/failure`, `flush_failure`, `optionB_interrupted_retry`, `optionB_every_write_prefix`); actual buffers/invocations/suffix and native syscall association remain **UNRESOLVED** where not already public. No delivered prefix erased. |
| _print/_eprint / print_to | Failure status and selected label + OS-error text/length **conditional public-only**, V400 (`print_to_message_public/length_public`). Full capture/global write_fmt, panic payload/hook/frame content and native association **UNRESOLVED**. |
| Dependency logger/level/environment dispatch | Configuration values, enabled level and route **conditional public-only**, V400 (`V400_logger`, `logger_reply`). Arbitrary logger code, witness-formatted arguments, mutable TLS/locks and complete reached cone **UNRESOLVED**. |
| Raw stderr metadata/flush/panic_output constructor | **NOT REACHED for diagnostic emission in those complete leaf bodies**, inherited source binding. Public outer locked flush handled separately under V400. panic_output does not run a hook or write. |
| Raw write_all Interrupted guard/error destruction | **NOT REACHED for extra diagnostics**, inherited valid OS/static noncustom representation. The prior syscall effects and retry suffix remain; status/retry dataflow conditional under V400. Custom error payload destruction **UNRESOLVED**. |
| Backtrace status accessor | **NOT REACHED for capture/symbolization/emission by accessor**, inherited proof; later use remains distinct. |
| Backtrace enablement / disabled branch | Environment/configuration selection **conditional public-only**, V400 (`V400_backtrace`, `backtrace_configuration_reply`); no create after normal false enablement, inherited. Native cache/concurrency/constructor occurrence **UNRESOLVED**. |
| Backtrace capture, PCs/frame selection/symbolization | **UNRESOLVED** witness/control-path/frame/order/formatter/resolver law. Public configuration does not make captured frames environment failures. |
| LazyLock poisoned destruction | **NOT REACHED for field/resolver execution in that branch**, inherited proof; earlier poison/panic retained. Other field drops/unwind **UNRESOLVED**. |
| Noncustom valid io::Error destruction | **NOT REACHED for payload-destructor diagnostics**, inherited proof; custom payload, allocator and unsafe-representation obligations retained. |
| strerror / UTF-8-lossy | Selected code, signal bytes and public pure renderer content/length **conditional public-only**, V400 (`V400_strerror`, `lossy_public/length_public`). Invocation/selected code, native conversion and non-OS/custom contents **UNRESOLVED**. Precursors do not fabricate emissions. |
| estimated_capacity / ensure buffer lengths | Literal template shape retains inherited local law; witness-derived operands, selected allocation sizes and actual invocation **UNRESOLVED**. They are not OS outcomes. |
| op227 formatting | **NOT REACHED on inherited scoped honest path**, b3p6 resume7; other panic sites unaffected. |
| General panic/default hook, OOM, double panic/abort | **UNRESOLVED** honest guard exclusion or public payload/size/frame/operation law. OS-triggered failure status does not publicize witness-derived payload. |
| Foreign writes, fatal signals/crash reports | **UNRESOLVED** configured reporter, reached-effect closure, bytes/PCs/registers/memory/payload law; not covered by the environmental status model. |

Capture short-slice panic stays NOT REACHED under the inherited finite normal callback/constructor association. Disabled/unsupported display is a public selected literal, with actual occurrence/delivery association retained. No checked same-public honest-witness leak was found. `DIAG_witness_operand_obstruction` is a model-level control showing that distinct returned operands remain observable; it is not such a native finding.

## Decoder handoff and endpoint accounting

`decoder-handoff.json` names the exact exports and read-only PV_RJ4IDB snapshot `2f5799d410e6f751d978f8bd0080ae3212a7a347`. That decoder is absent from this candidate. Instantiate `decode x := PV_RJ4IDB.decoder (PV_RJ4IDB.diagWithState expose x)`; `DIAG_complete_decoder/retained_state` retain both diagnostic and visible-state pieces. Existing `diag_events`, `diag_prefix` and `coupled_decoder` consume the joint pieces. No decoder is duplicated and no actual integration is claimed.

**Endpoint premises removed / added / weakened: 0 / 0 / 0.** Before: diag6's native event/terminal/prefix-family association and original L1 joint distribution were open. After: environmental model equations are instantiated, but complete native sourceBinding/public invocation/operand laws and actual observerOracle/runtime.disclosed recovery remain open. V038, V178/V181, V336–V339, V347–V351, V370 and V400 remain named. V229/V230/V256/V257 credit is untouched. T remains exactly entropy_law, entropy_kernel, observation. No endpoint, simulator, observer, trust definition, soundness cone, crates or programs were edited.

Next concrete deliverable: bind each covered public invocation/operand and exact OS reply sequence to the original native L1 history; prove V400's reached-failure independence/transport with V337/V338; separately discharge or exclude witness-derived formatter/panic/frame/logger inputs. Then integrate the existing decoder and complete observer recovery. The public-input theorem does not establish these by itself.

## Final verification

**100/100 Lean attempts**, 65700–65799: **91 pass, nine rejected/uncredited attempts**. **5/40 capped native scopes**, **0 Kani**. Stop: the Lean budget is exhausted. No full privacy-release regression, SBF/Aeneas/Rust rebuild or unchanged full replay ran.

Every scope records target, command, source/dependency hashes, source revision label, exit, wall, peak RSS, swap and axioms in `attempts.json` and individual receipts. Caps: MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64; Lean -M7000; one scope at a time. All actual launches have same-wrapper allowed:true AND admission exit0.

Aggregate scope wall **37.44s**, peak RSS **504,376 KiB**, swaps **0**. Accepted axioms are subsets of {propext, Quot.sound}.

| Audit | Target | Exit | GNU wall | Peak RSS KiB | Swap | Source revision label |
|---|---|---:|---:|---:|---:|---|
| 65797 | PV_DIAG7_Audit | 0 | 0:00.19 | 482900 | 0 | `8ad5d8093959d80496f2cd47384c8887eaf28824` |
| 65798 | PV_DIAG7_CohortAudit | 0 | 0:00.16 | 478244 | 0 | `8ad5d8093959d80496f2cd47384c8887eaf28824` |
| 65799 | PV_DIAG7_FinalManifest | 0 | 0:00.16 | 477464 | 0 | `8ad5d8093959d80496f2cd47384c8887eaf28824` |

65797 audits every new theorem and the adopted public-input specialization, printing the full native-handoff hypothesis. 65798 audits the signal/Program carriers and retained prefix/bound contracts. 65799 is the **single final diagnostic manifest**, not the frozen privacy-release manifest. The nine-object preflight and twelve-object final closure have zero source/object/dependency mismatches (`final-pre.json`, `final-post.json`); all 5,673 external authority objects were checked before compilation.

Rejected Lean sources: 65703 indentation; 65704 beta reduction before rewrite; 65748 dependent-match equality; 65753 indentation; 65757 ambiguous bind name; 65758 and 65759 over-unfolding of recursive run; 65770 the same over-unfolding at a write continuation; 65783 unqualified bind/pure simplification. Each was corrected before use, with its source snapshot and error retained. Signal/file-success refinement changed Signal and recompiled Effects and Program against it; no stale importer is consumed.

Admission for 65742 encountered a transient vanished-cgroup FileNotFoundError, allowed:false/exit78, before any compiler. One early retry hit the private wrapper's 180-second assertion and launched nothing; the later same-ID retry passed after the full cooldown. Both logs remain. **No VOID launch or cooldown-bypassed compile occurred.** Native01 rejected historical end-line-label interpretation; native02 checks exact body bytes and corrected spans instead. Native03/04 check closure identity; native05 removes only eleven private compiler objects. Sources, shared caches and receipts remain; no key/account/fund/nonce operation occurred.

`source-identity.json` matches all eight final modules byte for byte to accepted snapshots and their git blobs at **8ad5d80939**. Earlier revision labels identify launch state, while snapshots identify exact dirty inputs; they do not claim those dirty inputs existed at the earlier commit. All committed files are below20MB; no object, binary, archive, push or merge.

## Commits

```
8ad5d80939 Prove public diagnostic dataflow and preserve nonce and write outcomes
bace6e777a Model diagnostic environment inputs under adopted option B
```

The final commit records this reconciled report, decoder handoff and remaining audit receipts.
