# R250 selected private base execution

`AspisV8R19/R250PrivateBaseExecution.lean` compiled successfully. Private B::input returns Some exactly for raw words below P, and None otherwise; canonical encodings pass. Private B::half returns the exact half word on every raw word and x/2 on canonical field inputs. B::reduce returns the canonical field reduction for every U64. On canonical inputs B::mul equals the actual selected guarded M31 multiplication and returns encoded x*y. B::add/sub equal the selected raw wrapping helpers for all raw words. C::output converts the encoded pair exactly. This does not yet prove canonical add/sub results, C::input Option machinery, full private C arithmetic, Coeff110, batch, traversal or optimized acceptance.

Compile revision `26d6d454d6e0897fdf5d0fea9d5c119117602e05`; exit 0; wall 0:01.49; child peak RSS 3707172 KiB; swaps 0. All eleven complete reports use only propext, Classical.choice and Quot.sound. No new execution premise, sorryAx or native decision axiom. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r250-current-private-base-execution/manifest.json).

First remaining proposition: Prove canonical private add/sub and complex arithmetic, bind C::input/Coeff110 and actual inverse batch/traversal, then optimized-to-source acceptance.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
