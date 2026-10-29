# PV_DIAG5 — D452 resumed diagnostic work

Target not yet established. Branch `codex/pv-diag5-20261029`, base `b02602fa23`, exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-diag`.

## Stage 1: h5 double-prime source correction

`statement-identity.json` mechanically checks both declarations (complete binders, types and statements) byte for byte. The complete source delta is exactly removal of one `rfl` after the closing `simp only`, inside the second proof. `V2-proof-only.diff` records it. The unchanged signatures are SHA256 `6af2396122c81e6597df5cbf8a0ca1e29a563f6d7d8cd9e2881250051ba4dd80` and `839cf3145d8de676e6e3abbfebaa3d0ebcc1d256e21f36ab19872f5853d73f00`. Commit `e030a78a739b65afe67a6e2641be1c8b3e25cb70` supplies the tracked-history explanation; its parent is the EJR variant. Research, candidate, worktree and the fixing commit have the identical tracked bytes.

The EJR entry is **stale**: source SHA256 `4321909f01b6f4d578b5e4c2198ba59406418ef8bd85f6e177f34ae107ddb694`, blob `431494fb8678733178af8c5c58cb18fbcb49f3b9`. Under h5 double-prime the tracked source SHA256 `0bb8dcc74e6d33492d386582c06836aca1ee35fc61ce898cc3afb8f6d1b20e16`, blob `d555952917bff6d87a4701569e1da29e9042c338`, is the authority. Neither source was edited.

**65000–65010 all pass**: fresh tracked V2, then all ten blocked consumers fresh and unedited in `cohort-plan.json` order, ending in `PrivacyR1HeadlineDeployedReal` and `PV_RunJoin_Deployed`. Raw receipts contain complete source snapshots, direct dependency/sidecar hashes, command, exit, wall, peak RSS, swaps, revision and printed axioms. All reported axioms are subsets of `{propext, Classical.choice, Quot.sound}`. `cohort-preflight.json` checks 986 reused dependency objects and their recorded fingerprints; all 5,673 external objects pass before compiling. ID preflight found no collisions. Private sources/objects only; no shared replacement.

Two setup attempts failed before admission/compiler launch because this job initially selected the narrower TrustItems cache and omitted special endpoint roots. The traversal was corrected to use the full recorded resume cohort plus the eleven explicit source pins. These own-input preparation errors consume no Lean/native attempts. The recovered sampler generation authority from diag4 remains in force; no source or extraction was changed.

The stale EJR obstruction is resolved. This replay discharges no native privacy premise by itself. Further diagnostic work follows below.
