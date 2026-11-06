# Remaining obligations and early-stop justification

Target not yet established.19 row candidates are locally validated; authoritative ledger credit waits for the next lead gate. The baseline remains463 CLOSED /0 provisional /136 OPEN. No authoritative row was edited.

Budget used:39/100 Kani;64/100 Lean/link/audit scopes plus6 noncompiler preflight/support scopes (70/100 charged conservatively);1/1 extraction. No timeout or memory kill occurred. All heavy work had MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64; no cap or timeout was raised. This is an explicit below80-percent stop justification, not budget exhaustion.

The binding bottom-up/slice-boundary rules leave no unattempted independent member. All19 independent occurrences have complete candidate packets and the final gate. Repeating their unchanged proofs would not resolve a remaining obligation. Every remaining occurrence is listed separately below. No new in-scope Lean-only obligation can close one of these roots without its actual external child; the missing verifier entry/caller obligations are explicitly Lean-only in the sibling report, and are outside NJS scope.

| Remaining row | Member | Why no further admissible attempt can close it now |
| --- | --- | --- |
| TX1:081 | batch_merkle | Its actual batch_merkle_values child (TX1:082 / TX2:054) remains OPEN, transitively through batch_tree and verify_in_place. The sole-child wrapper cannot reach a CLOSED root before that dependency; an arbitrary operation dictionary is not a replacement. |
| TX1:082 | batch_merkle_values | Its actual batch_tree child (TX1:083 / TX2:055) remains OPEN for the verifier dependency. Composing the wrapper now would retain an unresolved child Result/endpoint, forbidden by (aq). No independent child remains within this member. |
| TX1:083 | batch_tree | Its real verify_in_place child is OPEN: TX1:127 / TX2:093. The merged NJP handoff explicitly lacks transaction-specific entry/wrapper, caller-domain and adopted-endpoint packets. Shared row/height/abort support cannot replace that CLOSED child. This out-of-slice dependency cannot be authored in NJS; bottom-up ruling forbids a parent certificate with a free verifier or successful-child premise. |
| TX1:084 | canonical_scan | Its real echeck child (TX1:189) is OPEN and outside the explicit NJS function list. NJC/NJJ partial cuts are retained read-only support, not a history-provider endpoint proof. Completing echeck would violate the slice boundary; a successful-history or arbitrary-echeck premise is forbidden. |
| TX2:053 | batch_merkle | Its actual batch_merkle_values child (TX1:082 / TX2:054) remains OPEN, transitively through batch_tree and verify_in_place. The sole-child wrapper cannot reach a CLOSED root before that dependency; an arbitrary operation dictionary is not a replacement. |
| TX2:054 | batch_merkle_values | Its actual batch_tree child (TX1:083 / TX2:055) remains OPEN for the verifier dependency. Composing the wrapper now would retain an unresolved child Result/endpoint, forbidden by (aq). No independent child remains within this member. |
| TX2:055 | batch_tree | Its real verify_in_place child is OPEN: TX1:127 / TX2:093. The merged NJP handoff explicitly lacks transaction-specific entry/wrapper, caller-domain and adopted-endpoint packets. Shared row/height/abort support cannot replace that CLOSED child. This out-of-slice dependency cannot be authored in NJS; bottom-up ruling forbids a parent certificate with a free verifier or successful-child premise. |

Future native/Lean requirements, without attributing a Lean-only blocker to Kani exhaustion:

- TX1:081 batch_merkle: After batch_merkle_values closes: compose SAME input, full Result and rejection prefixes. Native cut/control only if not already entailed by admitted wrapper transport; no missing Kani result is asserted now.
- TX1:082 batch_merkle_values: After batch_tree closes: bind the existing emitted body to its SAME child Result and complete native/source wrapper observation. No further native attempt is justified before the real child closes.
- TX1:083 batch_tree: After verifier admission: native arbitrary-prestate loop/branch/abort cuts with controls and Lean loop induction plus exact caller-domain composition. Shared NJP support may then be consumed from its merged source. This is not blocked by exhausted Kani; the currently missing sibling entry/caller obligations are Lean-only and out of scope.
- TX1:084 canonical_scan: First obtain a CLOSED echeck/history-provider child outside this slice. Then compose existing NJC/NJJ prefix/field cuts, full Result/history trace, and remaining native step/control and Lean induction if required. No claim that Kani exhaustion blocks a Lean-only proof.
- TX2:053 batch_merkle: After batch_merkle_values closes: compose SAME input, full Result and rejection prefixes. Native cut/control only if not already entailed by admitted wrapper transport; no missing Kani result is asserted now.
- TX2:054 batch_merkle_values: After batch_tree closes: bind the existing emitted body to its SAME child Result and complete native/source wrapper observation. No further native attempt is justified before the real child closes.
- TX2:055 batch_tree: After verifier admission: native arbitrary-prestate loop/branch/abort cuts with controls and Lean loop induction plus exact caller-domain composition. Shared NJP support may then be consumed from its merged source. This is not blocked by exhausted Kani; the currently missing sibling entry/caller obligations are Lean-only and out of scope.

All26 members accounted for:

| Row | Member | Final worker disposition |
| --- | --- | --- |
| TX1:065 | parent_with_digest | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX1:077 | private_leaf_hash_with_digest | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX1:078 | batch_key_at | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX1:079 | batch_keys | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX1:080 | batch_leaf | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX1:081 | batch_merkle | OPEN; exact blocker above. |
| TX1:082 | batch_merkle_values | OPEN; exact blocker above. |
| TX1:083 | batch_tree | OPEN; exact blocker above. |
| TX1:084 | canonical_scan | OPEN; exact blocker above. |
| TX1:086 | parse_shape | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX1:090 | same_batch_index | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX1:091 | same_batch_leaf | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX1:092 | slot | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX1:093 | sort_batch_keys | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX2:049 | private_leaf_hash_with_digest | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX2:050 | batch_key_at | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX2:051 | batch_keys | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX2:052 | batch_leaf | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX2:053 | batch_merkle | OPEN; exact blocker above. |
| TX2:054 | batch_merkle_values | OPEN; exact blocker above. |
| TX2:055 | batch_tree | OPEN; exact blocker above. |
| TX2:057 | parse_shape | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX2:060 | same_batch_index | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX2:061 | same_batch_leaf | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX2:062 | slot | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |
| TX2:063 | sort_batch_keys | Complete local candidate; no unproved local theorem remains; next lead ledger admission only. |

Latest sibling check: NJP merged at research 47477b58165; research ref at inspection a8863b281c90. Its merged final handoff retains BOTH verify_in_place rows OPEN. NJS_MERGED_NJP_INPUTS.json pins the read-only content; no sibling worktree was accessed. No other lane or pending runtime trust row is used.
