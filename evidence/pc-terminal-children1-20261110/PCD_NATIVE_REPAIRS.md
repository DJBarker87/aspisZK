# Owned native setup repairs
K001 stopped in metadata before Kani: missing frozen z4 workspace path dependency.
Repair: restore missing predecessor repair files only after verifying every byte against frozen 4bb3b3f5 git objects;
add them to the strict source pin validator. Never import predecessor harness modifications.
No lock rewrite, graph weakening, shared infrastructure change or prover verdict.
The next attempt has changed source/setup inputs. Original diagnostic retained.

PCD_Run scripts are owned validation/orchestration, not host infrastructure. E001 output recovery failed first on unescaped f-string braces, then on a missing local import in the recovery invocation; both were local Python errors, repaired without submitting a second extraction scope. No gate or validator was weakened.

K003 timed out at 180 s during dependency compilation, before Checking harness or CBMC. It has no semantic credit and will not be rerun unchanged. K004 isolates --only-codegen (compilation only, no solver); future verification must be separately scoped over the retained generated artifact or a further changed split. Caps/timeouts remain unchanged.

K004 code generation passes (no proof credit). K005 is the separate rejection-exit solver shape with unwind=1 and unwinding checks enabled: the exact checked-add mismatch precondition must prove that the native loop is unreachable. No same-command retry, larger timeout or renamed harness is used.

K005 reaches CBMC and FAILS on array::map input-constructor unwinding (loop 0, bound 1), not on the target contract. Repair input construction to eight explicit arbitrary M31 fields, preserving the exact unrestricted input domain while removing the constructor loop and function-pointer argument. No unwind increase, assertion removal or renamed target. K006 keeps the same contract/harness name and bound 1.

K007 fails type checking before a harness: the exact KMX module needs an alloc binding and allocator_api. Add extern crate alloc in the enclosing PCD-only module and a cfg(kani)-only allocator_api root attribute in the scratch tree; erase and validate that exact prefix against the frozen root on every run. KMX bytes remain unchanged. No shared infrastructure or shipped worktree source changes.

K013 fails an unwinding assertion in builtin memcmp on ONE fixed 32-byte digest comparison (bound10), before a semantic verdict. K015 isolates the same single outer iteration with the exact 32-byte standard comparison bound33. No outer frontier loop, source change, memory cap or solver-time increase is introduced; this is a fixed-array library comparison, not whole-frontier verification. No credit follows merely from this changed bound.

K015 was incorrectly mapped by the owned runner to the checked-rejection harness, not the intended frontier harness. Its receipt explicitly names that target; no frontier credit is claimed. Repair the runner to an explicit ID-to-harness table and validate expected_harness before launch. K019 will use the original unchanged PCD_frontier_contract name with bound33; no verdict-based renaming.
