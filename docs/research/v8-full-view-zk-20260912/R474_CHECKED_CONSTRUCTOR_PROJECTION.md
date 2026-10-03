# R472–R474: checked constructor projection

The three focused targets compiled on pinned Lean 4.32 with the cached
workspace, `-j1 -M4500`, MemoryHigh 5G, MemoryMax 7G, MemorySwapMax 0 and
TasksMax 128. Source revision: `c9602d7397efa038f1b31e9edf9b3ba043ee310c`.

| Exact target | Exit | Wall time | Peak Lean-child RSS (KiB) | Swap |
| --- | --- | --- | --- | --- |
| `AspisV8R19/R472CheckedConstructor.lean` | 0 | 11.51 s | 2,566,212 | 0 |
| `AspisV8R19/R473SequenceRegrouping.lean` | 0 | 1.20 s | 2,539,348 | 0 |
| `AspisV8R19/R474NativeConstructorProjection.lean` | 0 | 1.09 s | 2,537,004 | 0 |

Exact source checksums, saved sources, complete logs, all 25 axiom reports,
dependency source checksums, generator, source rows, preflight result and
failed attempts are in `evidence/r472-r474-checked-constructor/`. The successful
axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`, or no
axioms. The failed R472 and R474 attempts remain failures, including their
`sorryAx` reports; they are not used as proof evidence.

R472 strengthens R433's proposed allocation-fragment interpreter by checking
positive addresses at both fat and thin NonNull constructions. It retains the
complete constructor operation sequence, storage operations and both branch
arms; the current R440 readonly graph supplies the branch value. For a nonzero
input pointer it proves the complete fragment returns precisely `newIter`,
including rejection when the explicit pointer addition rejects. It rejects
null inputs, retains nonzero dangling empty inputs, and proves backed endpoint
construction and endpoint cast validity. Fragment rejection is `None`, not a
newly chosen Rust or verifier error.

R473 proves sequence reassociation and normalization preserve the complete
fragment control result for arbitrary initial locals: continuation state,
returned value and state, early stopping, and rejection. R474 uses these laws
to bind a generated syntactic projection to the complete checked constructor
fragment, rather than assume regrouping is harmless.

The projection reads the exact R440 input with SHA-256
`96135e91c71f93dcd3aeec7b693eb737e7cf05027456ca973242cf2586088c48`.
It checks all 28 top-level statements and eight statements inside both branch
arms, including cast source/target types and operands, pointer metadata,
pointer offset, marker construction, aggregate copy/move operands, return and
storage operations. The source rows and paths are saved. NonNull declarations
58 and 69 are checked for a single NotNull pointer field, transparent
representation, field offset zero, and captured x86_64 sizes 8 and 16.
Unknown operations or an input checksum mismatch are rejected. The saved
generator's `--check` passed against the promoted source.

This is a checked allocation-fragment theorem and a syntactic source binding.
It is **not** a certified JSON decoder, proof of Rust/LLBC memory semantics,
native ABI/transmute/metadata/offset correctness, source reference validity,
complete slice-fold or freeze execution, callback/oracle trace equality,
privacy, or soundness. The generated input projection does not turn R432's
allocation interpretation into actual Rust memory semantics.

The first remaining proposition is to justify the native primitive
interpretation and derive the memory and reference-validity relation for the
actual caller-produced slice. Then prove actual fold reads, pointer guards,
unchecked arithmetic, heap frame/lifetime, mutable callback restoration and
cleanup; Vec::extend and the Domain inverse failure remain separate. All
shared-oracle, universal joint-mask, simulator, extraction and probability-loss
obligations remain open.

Verifier source, the 999,790 / 999,532 CU results and every security parameter
were preserved. No CU benchmark or unchanged regression suite was rerun.
