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
