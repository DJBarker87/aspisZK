# R228: exact canonical half encoding

`AspisV8R19/R228HalfEncoding.lean` compiled successfully. The canonical half-word operation on an encoded M31 field element is exactly the canonical encoding of x/2. The result is canonical and its exact unreduced integer double is w+(w mod 2)*P. This connects R224 word algebra to the field encoding, but does not yet bind a selected Rust half declaration.

Compile revision `ab9260ef10d3b8895767a883fc5b42029ea8fc9a`; exit 0; wall 0:01.55; child peak RSS 3704716 KiB; swaps 0. All four axiom reports contain only standard foundations (propext, Classical.choice and Quot.sound). Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r228-half-encoding/manifest.json).

First remaining proposition: Bind the freshly extracted actual selected M31/CM31 half declarations to this word operation, then prove Coeff/LineCoeff construction and ordered four-array execution.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
