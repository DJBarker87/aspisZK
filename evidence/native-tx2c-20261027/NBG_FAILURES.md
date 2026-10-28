# Retained failures

K001: owned runner omitted deploying the immutable S2W_run_host.py into the new owned workspace. Admission succeeded and a terminal systemd scope ran Python, which exited2 before any Kani/compiler launch. No proof receipt exists. Launcher log and unchanged after-lock retained. Fixed OWN runner to install and byte-check the existing backends from NBC_LAUNCHER_INPUTS; shared host infrastructure untouched. K002 is the first actual Kani submission. This is a missing-input repair, not a timed-out or memory-killed proof rerun.

K002: setup-only JSON decoding error in own validation wrapper; no scope or Kani launched. Corrected serialization and added reverse dry-run verification to recognize the already-applied, byte-identical K001 patch. Validation is stricter than filename-based skipping.

K003: Rust lifetime compile error caused by a static raw pointer whose pointee contained a borrowed slice. K004 changes only the observation pointer to erased *const (); it is compared but never dereferenced. No Rust production source change. No solver launched by K003.

K004: the own patch preflight used patch -R --batch, which automatically reverses direction and misleadingly accepted an unapplied patch. The intended lifetime edit was not installed, and the same compile error recurred. Replaced preflight/application with strict git apply --reverse --check / git apply (no automatic reversal). No solver ran.

L001: residual pair let-pattern reduction after the Result rewrite; L002 adds the final definitional reduction. Rejected sorryAx diagnostic excluded from evidence.

L003: transport discriminant and checked Usize arithmetic need their named reductions; rfl alone rejected. L004 unfolds only those definitions and decides tiny constant bounds. No large numeral/recurrence reduction.

L004: checked Usize operations are noncomputable; deciding the entire Result equality is invalid. L005 uses existing Port4A_ReaderInstall.mul_value/add_value and tiny bound decisions, as the existing size_s2 proof does. Rejected diagnostics excluded.

L006: immutable launcher correctly rejected missing LPi_TowerValues before invoking Lean; no prover receipt. Missing unchanged dependency closure will be compiled once into the designated persistent cache, with original module source hashes; no shared object is overwritten. This is an input preflight failure, not a launcher repair.

L017: QM31 embedding needs the emitted ZERO constant explicitly unfolded; L018 supplies it. cm31_new already passed without axioms; no reuse of the rejected module object.

L019: digest canonicality left a Result/Bool conditional distribution goal. L020 splits the seven short-circuit tests and simplifies their branch hypotheses. The generic unwrap/projection and M31 decoder facts already elaborated; no rejected object is used.

L021: the full raw-limb decoder theorem left eight contradictory numeric branch cases; L022 closes them with omega after symbolic branch simplification. Other facts passed, including wrong-length rejection and raw canonicalization. No concrete field enumeration.

L024/L025: selected optional imports reference absent PAln_RowBounds. L026 building that unchanged source exposes missing Port5Q1_Ten through an existing retained dependency. Its21 missing unchanged source modules were located under the committed research lean tree (not another worktree); they will be built once serially in the persistent cache, if focused gates pass. No existing module or shared object is edited.

L055/L060: optional FIo_M31Values import continues into missing PAln_Physical and RawTx1DigestLog. Four unchanged PAln modules were recovered, but the new square-loop instance only needs LPf_BaseMultiply.source. L061 removes the broad FIo value import and derives its generic RefinesMul predicate directly from that reused exact natural-value theorem. No underlying multiplication/reducer theorem is re-proved or modified.

L067/L070: optional helper imports enter a legacy RawTx1DigestLog closure, whose source traversal reaches absent ExtractedSourceSemanticSampler. No XRn kit or stand-in is used or built. Getter ports now import concrete carrier Types directly. Two existing generic utility proofs are replayed verbatim under NBG_Utilities with minimal Aeneas imports (body hashes NBG_UTILITY_REPLAY.json); no NBC result or protocol proof is re-proved. L068 only lacked the lift/bind reductions; those are added without unfolding any scalar byte arithmetic.

L074: the atomic decoder's combined eight-word error normalisation exhausted the default200000 elaboration heartbeats at whnf. This shape is STOPPED and not rerun or given a larger limit. The mathematical graph is a nest of eight Result/Option branches expanded before their guards, not a large numeric recurrence. A future replacement must factor one word/residual-prefix lemma at a time before composition. Source retained as NBG_AtomicDecode_PROPOSAL.lean.txt and in L074; it is removed from importable lean/ and excluded from closure. K019 remains complete native evidence only.
L075: generic pack needed explicit unfolding before rewriting the existing tuple canonicality theorem. L076 fixes that one reduction; other model facts had no independent errors. Rejected sorryAx lines are not accepted.

L077: record field layout broke the local common-record constructors; subsequent change goals therefore could not identify them. L078 uses normal multiline record layout and folds the exact constructor before rewriting the common validator. The tiny VALUE_LIMIT shift law already elaborated. No changed domain or added hypothesis.

L078: fold is unavailable in the minimal tactic environment. L079 replaces it with a typed instance of the already-proved projection lemma and exact rewrites; no helper proof/domain changes.

L085: existential WideExact record projections in ew needed explicit unfolding for the final natural-value equality. L087 adds only ew to the final simp reductions; all source/canonicality obligations were already discharged. L081 was a diagnostic using the wrong namespace for the slice comparison instance; L083 prints the exact installed AspisR1TerminalDecoder compatibility instance and header body.

L089: optimized CM31 square input product and canonical bounds all proved, but the final modulo rewrite needed the named U64 size definition. L090 unfolds only UScalar.size/UScalarTy.numBits in that final bound; no field multiplication is evaluated in Kani and no resource limit is changed.

L090: unfolding U64 size leaves the fixed power2^64, which is not definitionally the decimal bound. L092 uses targeted norm_num on this one fixed machine-width constant, as LPf_BaseMultiply.word_product does; no large recurrence/finite universe is reduced and no limit raised.

L092: the generic size definition reduces to the still-opaque concrete U64.size. L093 adds U64.size/U64.numBits, exactly the existing LPf_BaseMultiply.word_product constant-normalisation list. No arithmetic domain changed.
