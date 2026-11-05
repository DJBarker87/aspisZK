# Resume codec association boundary

Frozen verifier.rs resume calls Reader.raw/e/k, validate_checkpoint_queries,
read_checkpoint_semantic_alpha, read_checkpoint_weights and heap::filled.
Reader.k calls QM31::from_le_bytes; Reader.e calls WideExact::from_le_bytes.
It does not directly call r1_wire::decode_k/parse_record/parse_record_at.

NGV/NGO are reusable upstream decoder/provenance packets. Their record-domain
laws cannot be silently substituted for checkpoint scalar calls: the original
checkpoint slice, exact offset, field byte domain, inner Checkpoint error and
reader cursor/backing must be transported separately. NIL_FreshOps and NID's
bounded reader laws expose this exact boundary. This is a call-structure
finding, not a claim that those CLOSED decoder packets fail, nor a change of
owner scope. Full native resume association remains required.
