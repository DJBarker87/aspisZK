# Multiplication abstractions and approved copy stubs

No NEV Kani harness substitutes or executes a field multiplication. Prefix append proofs call the actual Vec::push only. Field arithmetic is imported from NEI_/NEG_, never reproved.

| Native abstraction / stub | Paired Lean law | Domain and use |
| --- | --- | --- |
| Imported NEI_prefix_step::product_reply local record in NEI_K007/K008 | NEI_PrefixProduct.actual; NEI_PrefixWindows.specialize_field_reply | Every raw U32 lhs/rhs; actual emitted M31 multiplication returns ok with their natural product modulo2147483647 and canonical reply. The actual prefix read chooses the same operands; no field arithmetic is executed in Kani. These original receipts retain their names and domains. |
| Exact KMX_copy_nonoverlapping | Existing KMX_CopyMeaning loop/copy value laws, specialized by NEI_PrefixWindows.surviving_copy where needed | Valid disjoint pointer ranges and admitted typed representation. Exact upstream KMX patch/file hashes are checked per native run; matching negative controls are mandatory. This is a copy stub, not a field stub. |
| Exact KMX_realloc | Existing KMX_CopyMeaning.realloc_prefix | Valid allocation layout; successful reallocation preserves min(old,new) bytes and failure preserves original allocation. Prefix's active push has spare capacity and must not grow; capacity/pointer observations are proved. This is not a field stub. |

Patch sha256: bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. No custom copy stub, mutable static, Option<fn>, proof_for_contract, or stub_verified is used by NEV prefix proofs. No suspended/quarantined predecessor native receipt is restored.
