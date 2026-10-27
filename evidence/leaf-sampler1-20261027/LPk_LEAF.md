# LPk sampler native bridge

Status: OPEN — preparation. No top-theorem premise removed.

Target: frozen Rust `sampler::low_base_p_digits` at
4bb3b3f51e16b4525f1d10336e2b0bcbbd775387 to
`AspisR1Post25Sampler.sampler.low_base_p_digits`, cohort Funs SHA256
f02a8fc4503304c2630052a116be257ef507780ffe166844e1b08d71e0e9ec11.
Headline remains `AspisR1.RPx_Deployed.deployed`; this is one opaque-leaf
obligation under narrowed D188, not premise removal or a release claim.

Stages: (1) model step and composition; (2) native single step and reverse
writeback; (3) native-relation induction and cohort Result join; (4) from_fn
ordered shared capture; (5) four SDX fixtures.

Limits: 60 Lean attempts, 20 Kani runs; one admitted 6G/8G/swap0/64-task scope
at a time. Frozen lock before every Kani run; offline; unchanged hash afterward.
No shipped files may change. Existing SInt2 objects are reused read-only.

Read: root AGENTS security/proof discipline, common/local rules, S2 handoff,
plan, diagnosis, interface, C3-BIN route B and P6 rulings, owner amendments,
D188-P3 and SDX finding. Historical statements are superseded by the binding
owner amendments. No session A live worktree or candidate is edited.

## Stage 1
`LPk_Step.unique/machine_step/step_join` prove the bounded natural relation,
uniqueness and machine-model association. `LPk_Cohort.step_result` proves the
ACTUAL cohort step Result writes the quotient and satisfies that relation.
`LPk_Cohort.all_blocks` reuses the cohort's eight-limb/eight-digit inductions
and proves complete successful Results, ordinary digits, final quotient and
bound 256 on every block. Accepted receipts L003/L004; standard axioms only.
L001/L002 are rejected proof errors, repaired before acceptance (not timeouts).

K001 stopped at metadata: missing scratch dependency sources, no Kani launch.
K002 reached compilation and stopped on a missing unchanged include file.
The frozen include was copied; no dependency or frozen source was modified.

## Stage 3 (model composition)
L006/L008 pass. `LPk_Induction.pass_join/digits_join/eight_digits` induct over
arbitrary local step relations and ordered passes. `LPk_Result.native_result`
joins the decoded block, all eight digit carriers, final quotient array and
returned low limb to the cohort's complete Result. Its explicit trace input is
NOT yet derived for the frozen Rust: the native gate below remains mandatory.
All new top theorems have printed standard-axiom audits. L005/L007 were rejected
projection/word-bound rewrite errors, repaired before acceptance.

## Native arithmetic review
K005 timed out at the unchanged 90-second harness limit (wall 91.917 s,
328884 KiB RSS, swap 0). It asks q*P+r=packed dividend and r<P for one native
step on rem<P and arbitrary u32 limb. No division-equivalence assertion and no
field multiplication is present. This shape will not be rerun unchanged.
K003 first failed on another missing frozen include; K004 on the scratch module
path. Both are compile failures, not semantic failures. K005 repaired the path.
The scratch harness is retained as patches only (the earlier direct evidence
source file is removed); no repository crates/ or programs/ file changed.
