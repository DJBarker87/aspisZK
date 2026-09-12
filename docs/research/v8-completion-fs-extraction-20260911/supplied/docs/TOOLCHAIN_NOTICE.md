# Historical reproduction is not patched-kernel validation

The Aspis evidence inspected for this package records Lean **4.32.0**, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`.

During preparation, an upstream kernel fix was independently checked:

- Lean upstream PR **14498**, “fix: kernel to check opaque values for fvars”:
  https://github.com/leanprover/lean4/pull/14498
- Merge recorded by the upstream repository:
  `7346219967957ca3dd4302a75a849b67eed1b3cd`.
- Primary vulnerability advisory identifying the fix in **4.32.2**:
  https://www.vulncheck.com/advisories/lean-4-before-kernel-accepts-opaque-declaration-with-an-unbound-free-variable
- Upstream proof-validation guidance:
  https://lean-lang.org/doc/reference/latest/ValidatingProofs/

The upstream description says opaque declaration values were not checked for
free variables. An in-process metaprogram could exploit that omission to
produce False. The same description explains why the comparator export format
and a suitable independent checker protect against this particular defect.

**This does not show the Aspis proof files contain an exploit or invalid proof.**
None is alleged here. It does mean that a 4.32.0 green build and standard axiom
list should not be the last independent validation layer.

Keep two separate environments:

1. The historical pinned environment, read-only where possible, for reproducing
   the exact recorded result. Label its output HISTORICAL_COMPILE_ONLY.
2. A separately pinned compatible patched environment, at least 4.32.2 for this
   issue, with the appropriate Mathlib revision and a clean first-party rebuild.
   Re-run axiom audits and fresh replay. Prefer comparator plus an independently
   implemented kernel as a further layer. Verify current advisories before final
   sign-off; the minimum version screen is not a blanket claim of kernel safety.

Do not change the user's running worktree, silently substitute Mathlib, or
rewrite old logs. A proof port to the patched compiler must have its own diff,
manifest, output hashes and checked statements. A custom backport requires
reviewed source evidence, not merely a version string claiming compliance.

The supplied build runner requires an explicit expected version. Normal
validation refuses an identified version below 4.32.2. Historical reproduction
requires the explicit `--purpose historical` mode and cannot be passed to the
pack's kernel-certification stage as a validated build.

No kernel proof-of-concept or exploit is included in this package.
