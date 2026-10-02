# R326: exact sequential prefix product selectors

`AspisV8R19/R326PrefixProductSelectors.lean` compiled successfully. Every in-range element of the R321 prefixValues recurrence encodes the exact sequential prefixAccum product. For any output vector equal to the original vector followed by this recurrence, the selector at the corresponding appended index returns that encoded product. The shift theorem relates the two recurrence indexings. Zero products are allowed. These are algebra/list selector lemmas; the exact output equation is an explicit premise, and no caller, nonzero or full batch argument is claimed.

Compile revision `d4bf07b08443136de0a11fc1fd932bd604586c2e`; exit 0; wall 0:01.54; child peak RSS 3713760 KiB; swaps 0. All three complete axiom reports use only propext, Classical.choice and Quot.sound; no sorryAx, native proof or new execution assumption. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r326-current-prefix-product-selectors/manifest.json).

First remaining proposition: Derive source batch initialization and prefix output invariants, use these selectors to supply the reverse-loop prefix reads, and connect total inverse and output initialization. Actual chain/any/default try_fold extraction, independent Rust-library/compiler correspondence, freeze fold/extend, full callback/privacy/soundness remain open.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
