# Sole raw diagnostic failure

The prior source-only preflight remains PASS and was not repeated. The lead's
exact terminal release resolved the old coordination condition. This failure
occurred later in a NEW local diagnostic source; it is not a historical
ROOT/source-export failure or a current-A data absence.

Exact executed source is Port28ROOTEXPORT_Raw.lean, SHA256
c2bda01767294e5a526c4001855b011dab1586578c228583906b9e7d916ef393,
committed f75d0fc644. The source is preserved unchanged. The single invocation
was charged before launch; no retry or second elaboration occurred.

Exit1; wall4.756840041838586s; time(1) maximum RSS1,285,439,488B;
monitor aggregate peak1,280,819,200B; swap0. Exact command, source revision,
core/sysroot/runtime/input hashes are in lean.receipt.json and the retained
4,496,634-byte diagnostic-inputs.json. Axioms N/A: data diagnostic, no theorem.
The elaborator's generated error placeholder was rejected by ordinary #eval;
there is no sorry/admit/axiom token in the authored source and #eval! was not used.

The first error at57:74 is the record-update layout: fields following the
inline `data with imports := #[]` did not parse. The separate coreNames fold
at77:2 leaves the numeric accumulator type ambiguous. Evaluation was rejected,
so no mainDiagnostic IO, raw header scan, ConstantInfo selection, transport,
closure, or duplicate-declaration comparison happened. All copied input files
remain retained; no transport directory exists.

Proposed source corrections, NOT compiled or represented as validated:

- Use the accepted Port18 layout, with `data with` followed by one indented
  field per line: imports, constants, constNames, extraConstNames, entries.
- Annotate both ownership-forcing folds with an explicit Nat accumulator
  `(0 : Nat)`, as the accepted Port18 source does.

A separately allocated diagnostic invocation is required to validate those
changes and actually obtain emitted/group/type/value data. The five consumer
slots remain held and untouched; none was borrowed to fix this error. No host
compiler/build/scope, project import, trust/environment mutation, backend,
extraction, ELF or theorem campaign occurred.
