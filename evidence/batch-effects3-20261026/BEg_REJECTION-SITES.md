# Emitted rejection site inventory

Static inspection of retained Port3_NativeBatchBody, with the four none-return sites already present in the pinned lowering (no new source behavior asserted):

| Native source site | Retained lowering | Reads before terminal exit |
|---|---|---|
| duplicate leaf mismatch, candidate.rs186–188 | explicit some(Err Merkle), Lean123–124 | includes the duplicate leaf hash before comparison |
| missing node_count, candidate.rs196 | none after residual, Lean176–180 | all reached leaf calls; no subsequent parent |
| overcapacity count, candidate.rs199–200 | none, Lean149 | all reached leaf calls; no subsequent parent |
| nonzero whole-word padding, candidate.rs199–200 | none, Lean163 | all reached leaf calls; no subsequent parent |
| verify_in_place false, candidate.rs202–203 | none after returned scratch, Lean175 | includes the complete actual reached parent-call prefix |

The enclosing emitted tree decodes none as outer fail panic at Lean227–228. Rust emits inner Parse or Merkle. The owner's success-conditioned rule permits the error-kind distinction after proving common source prefix, same acceptance and query/effect transport. The table is syntax inspection, not a kernel proof of all native paths or their physical histories. BEf already pins the padding site's extraction provenance and native reachability. No new acceptance vulnerability is asserted.
