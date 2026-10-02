# R227 vector-projection translation diagnostic

One capped Aeneas translation was run on the exact R220 schema-audited incomplete projection (input SHA-256 `5bff089f4502d4a3a6bf90cb679807e25265d309ca9c509976996a62be26551b`) with the audited R215 `aeneas-copy-operands` binary (SHA-256 `7e3be7b0c24975c248ad769c80bac2cc896a5f1b89c2858b8f01a6024cf80ae3`). The binary was copied unchanged. The lead-specified source revision is `ab9260ef1`. Exact argv, launcher argv, caps, reservation snapshots, complete combined tool log, and result metrics are recorded here. No binary copy is retained in this local evidence bundle.

The child exited 2 after 0.17 s, peak RSS 54,912 KiB, swaps 0. Its first reported failure is `Charon__TypesUtils.type_decl_get_fields` (`TypesUtils.ml:66–68`): it cannot obtain fields for opaque core `MaybeDangling` ADT type ID 63 while interpreting an aggregate; the stack passes through `InterpExpressions.eval_rvalue_aggregate`. No generated directory was created. The full error and type declaration are in `translate.log`.

The projection input and R220 inherited unresolved vtable references (Global IDs 24, 28, 51) were left unchanged. This is a diagnostic only, not a source-semantics result or proof evidence. The translation was not retried.
