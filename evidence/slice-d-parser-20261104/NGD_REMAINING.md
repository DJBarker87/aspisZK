# Remaining members

slot_offset CLOSED (2 rows); four members OPEN. Native/model/domain and coherent audit packets are required.

- slot_offset: CLOSED. Exact source returns usize, with caller domain slot <= 6. The emitted all-offset panic theorem is retained for slot > 6. See NGD_CLOSED.json.
- decode_k: preserve original payload windows and token provenance, checked multiply/add/get, N=1/28/29, first NonCanonical and exact full Error.
- parse_record: valid framing, original borrowed payload, row_shape and full-error validator substitution; all error paths.
- parse_record_at: frozen source uses offset + length, NOT checked_add; row_shape unwrap requires valid row. Derive no-overflow at every caller and preserve original framed window and full parser reply.
- expand_semantic: original 27-row schedule, same output windows, disjointness/frame, first error; native iteration and Lean induction.
