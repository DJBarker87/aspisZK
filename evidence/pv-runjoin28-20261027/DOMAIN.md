# Exact checked inner domain; outer boundary retained

For all input/out/recipient/change/public/laneAnchor/snapshot values and all
ExternalLinear/Records dictionaries, CompilerDomainProof28.success_iff proves:

    (exists compiled, compile_forest_from_copies args = ok (.Ok compiled))
      iff CompilerDomain28.Path args.

Path contains no call to the compiler, no admission assumption, and no cached
compiled field. It expands every primitive return and compiler guard into
explicit existential equations and branch conditions. A primitive panic or
divergence is not silently treated as a successful Rust Result. Both native
Result layers are retained.

For every error e, RejectionProof28.error_iff proves:

    compile_forest_from_copies args = ok (.Err e)
      iff CompilerRejections28.Path args e.

The error predicate names each exact error constructor at its actual branch,
preserves every earlier successful primitive/guard, and retains Try residuals.
It characterizes first-error precedence. It does not promise that a later
failed check wins over an earlier failed check. The predicates and theorems
are universal, not fixture facts.

This is an operational domain, not a proof that all these checks follow from
RspendPlus. For the two OUTER wrappers, native preparation additionally takes
runtime context/spent-nullifier state and a live snapshot. A set of semantic
statement/witness pairs alone cannot discard this state: for example, changing
only whether the nullifier is already spent changes admission. The final
preparation domain must keep these parameters or prove their intended honest
construction/association. GUARDS.md records the ordered outer checks.

No complete outer-wrapper source theorem, semantic simplification of all
inner checks, or canonical preparation-domain coverage theorem is claimed.
The frontier finding shows why successful raw-wrapper output cannot simply
stand in for the missing canonical input provenance. The original checked
HonestInput family remains unchanged.
