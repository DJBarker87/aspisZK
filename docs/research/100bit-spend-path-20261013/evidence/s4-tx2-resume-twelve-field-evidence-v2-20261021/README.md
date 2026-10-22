# S4 tx2 resume to candidate twelve-call field evidence

`resume_model_candidate_twelve_actual_field_evidence` refines the prior tx2 prefix result. For each of the twelve reached query states, it preserves the actual successful `candidate.queryWithOps` call and attaches `CandidateQueryFieldEvidence` derived from that same call. The evidence includes the actual dots callback output equality, canonical four outputs, the strict-scanned 832-byte opening slice, and four literal field results. The powers array and `ClaimPowers` vector are the same witnesses already obtained from the successful source prefix.

The theorem still covers only the explicit selected `resumeWithOps` model, split guard, and powers-through-query-loop prefix. `ResumeOps`, geometry/pending operations, strict scan success, and prepared gamma canonicality remain upstream contracts; this is not full `tx2_common` or `tx2_authenticated` Rust correspondence. Candidate QueryOps and P6/std boundaries remain as stated in the imported field-evidence producer.

The first v2 attempt stopped during import setup because the producer's transitive Lean path was omitted; it is retained under `evidence/diagnostics/attempt-v1/`. The successful focused rerun used the producer's complete recorded LEAN_PATH plus the prior tx2 selected closure.
