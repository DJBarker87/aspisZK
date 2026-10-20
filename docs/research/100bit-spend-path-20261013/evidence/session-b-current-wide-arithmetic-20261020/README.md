# Current WideExact extraction and arithmetic bridge

PROVED: selected current WideExact operations are extracted from byte-exact frozen field.rs and wide_exact.rs with no opaque lower-field operations. The complete selected Types/Funs are checked after removing resource overrides only. The scalar M31 operations and CM31 add/sub/mul/mul-by-r graphs equal the previously proved current arithmetic under an explicit record conversion. Exact new QM31 add/mul graphs are likewise connected to the retained arithmetic owner, then to its canonical exact-field semantics.

PROVED: successful actual WideExact addition preserves canonicality and decodes to addition in the retained degree-eight field. Input canonicality remains explicit; each actual component-call success is derived from the source result. No backend operation-law premise is introduced. Subtraction, scalar multiplication, outer multiplication and the final FoldOps instance remain work in progress.

Six focused NUC targets, fifteen standard-only theorem reports, -M4400/defaults, High1GiB/Max2GiB/Swap0. Charon/Aeneas use High512MiB/Max2GiB/Swap0, release/jobs1. Exact retained QM31 decoder/tower and source owners are reused. No production change, binary artifacts or full replay.

OPEN: remaining WideExact operation laws, canonical actual caller values, conversion into the separately extracted fold ABI, whole frozen stage-2/caller/runtime and the complete 100-bit theorem. The extraction itself is source evidence; this packet does not call every extracted arithmetic operation proved.
