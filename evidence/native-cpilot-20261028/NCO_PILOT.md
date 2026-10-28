PILOT RESULT: pending.

Selected slice: parser, starting with row_shape → parse_record → parse_record_at.
The additional Prefix accessors are independent small interface probes. Validator
and expansion leaves retain their recorded CLOSED domains, subject to K-1
revalidation for copy-dependent evidence. No historical leaf result is being
promoted to a function-contract proof.

Stages: (1) pins, interface controls and references; (2) leaf contracts;
(3) callers; (4) extracted-reference Lean equalities; (5) final audit.
Each stage is committed. Budget: 70 Kani, 60 Lean, serial capped scopes.
No changes to shipped source or existing Lean modules are authorized here.
Headline and all approved trust boundaries remain unchanged; S2 OPEN.

Stage 1: interface probes K001–K014 show Result<u8,u8> fidelity controls
behave as required. Bare &[u8] and Result<&[u8],u8> contract body checks pass,
but stub_verified code generation rejects &[u8]: no kani::Arbitrary impl.
K011/K014 are compiler failures, not intended assertion failures and not
fidelity passes. No workaround or carrier replacement is silently admitted.

Stage 2: frozen row_shape contract K025 PASS; call-site substitution K026
PASS; wrong caller assertion K027 FAIL; inverted actual contract K028 FAIL.
Frozen compact_row K029 PASS; call-site K030 PASS; K031/K032 controls FAIL.
Option<(u8,usize)> controls K033–K037 complete: weak contract and real-body
assertion PASS, unimplied assertion and inverted ensures FAIL, frame violation
FAIL. No Option<fn> is reached.

E003 extracts row_shape_ref/compact_row_ref successfully with Charon companion
sha daad69be… and Aeneas c0cf4fcc… (b59d5188 extended); source and commands are
in NCO_EXTRACTION_PINS.json and E003 receipts. E001/E002 are excluded failures.
Generated Types/Funs compile L001/L002, no theorem axiom audit applicable.
