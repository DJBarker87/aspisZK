# Runjoin33 continuation

Entry: `4d99d31c672692d1d2938922fcb383087ca89b1f`, branch
`codex/pv-runjoin-20261026`, exact assigned worktree.
Authorized merge: `df13941c50f1679304bd1aef4346dae8df81fb02`, completed
without conflicts at `f18cb491c92bc8a08955af0ce119d561f7857b35`.
No conflict resolution. No pushed commits.

Budget: 100 Lean starts, zero Kani; IDs 51800–51899, audits 51897–51899.
Reuse runjoin32-lean objects; no unchanged coherent rebuild or prior audit rerun.

Order: actual emitted complete Result to security model at canonical callers
(V163/V165/V045), actual initialization/effects and both ROMView decoders
(V167/V038), then unchanged coupling and bad/query events into
RustRealRefinement. Source erasure and native extraction trust remain distinct
from security-model and deployment association. No endpoint premise removed yet.

The merge imports nine changed crate paths, all byte-identical to source at
763e429f184b932ca5c52633b7fa2a98a3b36b6f (`git diff --quiet` exit 0 for
crates/programs). Its inherited batch2f/ELF-GATE.json records all three release
ELFs matching the prescribed pins at that revision. No new Rust/extraction/
structural gate is run or deployed credit inferred from non-deployed features.
Any new such gate must satisfy lead ruling (x): devnet_spend release, Rust
1.94.1, r1p-check and aspis-r1-cost-probe/ct-host-prover, resolved features for
every crate; verifier artifacts use their respective deployed configurations.

## Correction to the historical ELF paragraph

The identity claim above is WITHDRAWN. Its shell invocation did not capture the
diff command exit separately; the explicit final check exits 1 and lists 21
crate files differing from the historical gated revision. See
merge-source-identity.json and FINDING.md. Historical pins do not validate this
merged tree. No deployed credit is claimed.
