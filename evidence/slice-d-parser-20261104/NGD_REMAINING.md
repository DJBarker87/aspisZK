# Remaining members

All five members OPEN. Native/model/domain and coherent audit packets are required.

- slot_offset: frozen body returns usize, loops over SLOT_NODES, and panics at slot > 6. It does not return Result. Prove 0..6 exact values; prove arbitrary prestate step/overflow and classify out-of-domain panic.
- decode_k: preserve original payload windows and token provenance, checked multiply/add/get, N=1/28/29, first NonCanonical and exact full Error.
- parse_record: valid framing, original borrowed payload, row_shape and full-error validator substitution; all error paths.
- parse_record_at: frozen source uses offset + length, NOT checked_add; row_shape unwrap requires valid row. Derive no-overflow at every caller and preserve original framed window and full parser reply.
- expand_semantic: original 27-row schedule, same output windows, disjointness/frame, first error; native iteration and Lean induction.
