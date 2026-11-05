# Failed steps and replacements

K001/K002: native filled harness failed compilation: exact KMX includes allocator_api. Replaced with scratch-only cfg(kani) feature attribute. No semantic control credit. K003: own unified-diff reader appended the attribute in the wrong location. Replaced with context-checked unified-hunk application; K004 PASS/K005 semantic FAIL.

L001: reserved Lean identifier prefix and nonexistent ReservationError type; L002/L003: list-append proof normalization. Fixed statement/proof, no resource increase. L004 passes. Draft elaboration sorryAx outputs are excluded.

K016: partial local-record window failed unwinding while generating arbitrary2048-byte input; not a timeout, not a mismatch. Bound18 did not cover initialization. Replacement exact bound2050; no stronger input precondition and no timeout/cap change. No credit until replacement and matched control pass.

Stage native byte-window review: K045–K060 cover j<16 only, while S2 callers request n=64. This is a stronger precondition than the caller establishes. No TX2:141 closure from these gates. Replacement must widen scratch and j together to64; same harness names retained, and matched controls rerun for the changed domain. This is a new domain obligation, not an unchanged passing-shape rerun.

K079 init01: CBMC timed out at90s (scope wall95.86688469s, RSS6345004KiB, swaps0), proving combined length/new cell on an unnecessarily independent64-cell prestate. No credit; no rerun unchanged. Replacement restricts the prestate to the ACTUAL filled initialization invariant: an arbitrary prefix p<64 of the SAME arbitrary value. NHM_Filled64.initialization proves that every caller iteration supplies exactly this invariant. No stronger-than-caller condition, no cap/timeout increase, same harness names. Existing broader pointer/move K077/K078 is reused, not rerun. Frame law now concerns the initialized prefix of this owned fresh vector; it never claims arbitrary caller-visible aliases.

K080 init01 also timed out at90s (scope wall92.71154494s, RSS6347864KiB, swaps0); no credit. The SAME-value invariant alone did not eliminate the64-push to_vec setup cost. Replacement changes only prestate construction to with_capacity(64)+resize(p,value), then the ONE target resize(p+1,value); splits value/frame observations by limb. Same actual initialization invariant, same original init01 name, unchanged90s/caps. No failed shape resubmitted unchanged; broader pointer K077/K078 still reused.

K081 init01 (single limb, direct Vec resize prestate construction) timed out at90s (wall92.81269740s, RSS6342920KiB, swaps0). All three shapes are excluded, no cap/time increase. Filled TX2:045 remains OPEN: actual returning allocation/pointer facts and full model/encoding/frame induction are available, but native symbolic-prefix initialized-value/frame association is not. Next work must isolate the std resize write window further or obtain a specific admitted std/allocator transport; no success/availability premise is introduced. Init02 frame under the same costly setup is not submitted; proceed to the independent reserve-prefix observation and then partial/high/byte/group native work.

K111 weight04: unwinding assertion in builtin-library memcmp loop0, not a semantic frame mismatch or timeout. The weight equality compares512 bytes of the SAME immutable low tensor; bound66 was insufficient for the diagnostic assertion itself. Replacement exact bound514 for weight04; the separate384-byte accumulation coefficient frame uses bound386. Other passing body shapes are reused, never rerun. Accumulate02 now checks the right product operand, result, call count and full immutable coefficient frame together, avoiding an otherwise unpaired final budget slot. No timeout/cap change.

L025 WindowBridge: import owner collision: generated enum Error's discriminant attribute created global instDiscriminantErrorIsize before loading the coherent cohort. No closure or false coherence claim. Replacement retargets ONLY the new extracted reference enum names to NHM_WindowError/NHM_ControlError, with exact type/function token renames and import names; original extracted sources and hashes retained. No constructor, branch or Result/effect change; no existing proved module edited. Recompile the changed new type/function modules, then bridge and combined scan. This avoids reserving an unprefixed generated owner in concurrent forests.

L059 first wrapper input rawscan was rejected before launch by the own target allowlist; corrected to NHM_rawscan. Admission/preflight retained separately; no formal budget charged for preflight. The actual L059 scope raw audit passed188/188 standard-only roots, then scan exited1 solely on expected-import mismatch in all30 owned modules: catalogue omitted Lean's implicit Init (loader canonicalization includes it). No dangling references or incompatible owners. Failed scan retained at NHM_L059/NHM_LOADED_scan.jsonl. Fix the EXPECTED input schema to prepend Init for source files without prelude; the scanner and all rejection predicates remain unchanged. No closure credited on L059. Final audit is deferred until the remaining independent Lean work changes the combined source, avoiding an unchanged raw replay.

## Complete failed Lean draft inventory

All failed drafts are excluded from credit, including any error-recovery sorryAx. These are local elaboration/proof-shape failures, not accepted successful-child premises. No Lean timeout or memory kill occurred. Exact assertions and section6 metrics remain in each attempt log/receipt. Each replacement changes the source; final raw closure checks only the successful current modules.

| Stage | First diagnostic | Successful changed replacement |
| --- | --- | --- |
| NHM_L001 NHM_FilledFrame | : unexpected token 'prefix'; expected '_' or identifier | NHM_L004 |
| NHM_L002 NHM_FilledFrame | : Type mismatch: After simplification, term | NHM_L004 |
| NHM_L003 NHM_FilledFrame | : omega could not prove the goal: | NHM_L004 |
| NHM_L006 NHM_HighDot | : unsolved goals | NHM_L007 |
| NHM_L010 NHM_ArrayCanon | : omega could not prove the goal: | NHM_L011 |
| NHM_L012 NHM_DotFinishCanonical | : omega could not prove the goal: | NHM_L014 |
| NHM_L013 NHM_DotFinishCanonical | : omega could not prove the goal: | NHM_L014 |
| NHM_L017 NHM_DotLoopDomain | : Application type mismatch: The argument | NHM_L020 |
| NHM_L018 NHM_Filled64 | : unexpected token 'initialize'; expected identifier | NHM_L019 |
| NHM_L021 NHM_DotCallDomain | : omega could not prove the goal: | NHM_L022 |
| NHM_L025 NHM_WindowBridge | : import AspisR1FinishRelationCurrent.Types failed, environment already contains 'instDiscriminantErrorIsize' from NHM_WindowTypes | NHM_L028 |
| NHM_L029 NHM_ResultInvariant | (lean.unknownIdentifier): Unknown identifier value | NHM_L030 |
| NHM_L033 NHM_GroupWeight | : Tactic rfl failed: The left-hand side | NHM_L034 |
| NHM_L036 NHM_GroupCoefficientDomain | : Expected type must not contain free variables | NHM_L037 |
| NHM_L040 NHM_ControlLoop | : Tactic split failed: Could not split an if or match expression in the type | NHM_L043 |
| NHM_L041 NHM_ControlLoop | : dsimp made no progress | NHM_L043 |
| NHM_L042 NHM_ControlLoop | (lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of .done could not be determined | NHM_L043 |
| NHM_L044 NHM_GroupAccum | (lean.unknownIdentifier): Unknown identifier NHI_Scalar.zero | NHM_L046 |
| NHM_L045 NHM_GroupAccum | : Tactic rewrite failed: Did not find an occurrence of the pattern | NHM_L046 |
| NHM_L048 NHM_GroupRoot | : Tactic rewrite failed: Did not find an occurrence of the pattern | NHM_L049 |
| NHM_L050 NHM_GroupDomains | : Application type mismatch: The argument | NHM_L051 |
| NHM_L059 NHM_rawscan | NFN_SCAN_FAILED | NHM_L080 |
| NHM_L062 NHM_FactoredTerm | : Type mismatch | NHM_L064 |
| NHM_L063 NHM_FactoredTerm | : Type mismatch | NHM_L064 |
| NHM_L074 NHM_RegularDomain | : don't know how to synthesize implicit argument b | NHM_L075 |
| NHM_L076 NHM_FactoredFrames | : Application type mismatch: The argument | NHM_L077 |

Final L078/L079/L080 pass. The own validator initially used a no-op wrong-import mutation ([] on an already empty list); NHM_VALIDATOR_REPAIR.json records the effective append mutation. The acceptance gate was unchanged; all14 effective corruptions now reject. No formal rerun was needed.
