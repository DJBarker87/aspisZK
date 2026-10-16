# Terminal verifier translation candidate

Aeneas now translates an isolated modified-source candidate containing the
actual `Public.terminal_qm31` call graph. This is a translation checkpoint,
not the terminal semantic theorem or an adopted production change. The
[review archive](../evidence/terminal-qm31-extraction-20261016/translation-audit/README.md)
retains the unsuccessful attempts as well as the successful output.

## What overcame the translation failures

The original dependency extraction reached an optimized field loop containing
an unsupported outer `continue`. A local extraction crate instead includes
the same production source bodies as local modules and uses built MIR. That
removed this obstacle without changing the field arithmetic.

Aeneas next failed while tracking borrows in the nested Poseidon external
matrix loop. An isolated candidate factors each four-input matrix row into
a small private helper and makes the four output writes explicit. The input
snapshot and matrix formulas are preserved in the candidate diff; production
Rust remains unchanged. Equivalence and compute cost still need their own
checks before any adoption.

Translation then reached a generated-name collision between the `M31` type
and its Rust tuple constructor. The final adapter changes only
`translated.fun_decls[236].item_meta.attr_info.rename` from `null` to
`M31_constructor`. The lead independently compared the complete parsed LLBC
objects: all bodies, signatures, types, numeric IDs, references and declaration
ordering remain unchanged. The original LLBC is retained.

The final Aeneas run exited zero in 8.78 seconds, with 317,524 KiB peak process
RSS and no process swaps. It ran in a 4 GiB MemoryHigh / 6 GiB MemoryMax /
zero-swap scope. The transient cgroup peak counter was not retained.

## What the output does and does not establish

The output contains 221 function records: 201 local definitions and 20 opaque
external-library declarations, plus 59 type records including one opaque
external type. The generated external templates use axioms as placeholders;
they are not admitted proofs or behavior specifications. The terminal entry,
composition, optimized field multiplication and candidate matrix helper are
present as local definitions.

An initial direct-name reference scan counted 151 function records, including
14 opaque declarations. The lead rejected that as a complete reachability
argument because trait dictionaries and callbacks can add edges. The audit
now conservatively retains every emitted record. No external declaration is
classified as unreachable by that scan.

The existing mask arithmetic and prepared-multiplier proofs provide the main
reuse route. Generated declaration comparisons identify matching field
operations and six shared types; a deterministic import split still needs
its own checks before reusing those declarations in the terminal module.
Historical `Array.map` and `Result.map_err` models were also recovered.
Their exact signatures and source-correspondence limits must be respected.

The next focused proof starts with the exact generated row callback body,
whose arithmetic does not need the external `from_fn` or array-map wrappers.
Then it must establish wrapper sequencing, field reduction, the parent
matrix layer and the terminal relation. A small source slice can establish a
component theorem; it does not replace the complete terminal definition.

Full terminal compilation with concrete library models, semantic refinement,
candidate source equivalence, accepted-input canonicality and fresh runtime
measurements remain open. This checkpoint makes no new security or CU claim.
