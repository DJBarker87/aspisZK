# Stage 0: frozen endpoint inspection

Target is AspisR1.Rc7_Top.deployed. The source snapshot is SCF_BEFORE.lean.txt.
No target or implementation changes. Ledger baseline inherited from RPx: actual
83T/26P/13G/0C; deduplicated deployment-inclusive89T/31P/13G/0C;
all audit rows89T/32P/13G/0C. Baseline hashes are in SCF_BASELINE.json.

The literal binding is consumed by FGl_Bound -> F3U_ConditionalBound ->
F3U_RuntimeMass. Replacing it requires a same-H event implication and cannot
be accomplished by merely applying Rc7_Top.deployed to a different runtime.
SCE_Experiment supplies the shared adaptive account domain; its second-choice
queries occur between native stages. SCE_Annotation is a known-suffix theorem,
not an arbitrary deletion theorem. RPx_AccountCharge supplies the original
account recorder budget; FGl_Join's charged recorder is a different program.
Their equality/transport must not be assumed from matching numeric bounds.

All requested initial handoffs were read (older S2 paths resolve under
 docs/research/100bit-spend-path-20261013/). No live foreign worktree read.
No shipped source, cfg(kani), key or binary changed. ELF rebuild is inapplicable.
