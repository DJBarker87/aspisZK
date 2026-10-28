PILOT RESULT: partly. The end-to-end parser slice is NOT established.

Do not switch all lanes yet: the pinned Kani cannot substitute borrowed-slice
or Vec returns; complete loop-leaf contracts are also missing. Scalar contracts
and one-window expansion are useful partial results, not parser closure.

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

Stage 3 model-side result: L009 PASS, 1.377266791 s, 2642156 KiB RSS,
swap0. NCO_ScalarBridge.row_shape and compact_row identify the ACTUAL
Aeneas E004 reference extraction with the adopted S1NativeCompact cohort
functions on ALL u8. Both printed axioms are exactly
[propext, Classical.choice, Quot.sound]. No additional premise.
Earlier L003–L008 failed drafts are excluded; L004/L006 hit the default
heartbeat limit and were changed/split, never rerun unchanged or given
higher limits. E004 changes the reference's if tree to a matching Rust match;
K040 rechecks the native contract on that new reference. Its call-site and
negative-control rechecks remain required before final scalar credit.

Stage 4 native disposition: 70/70 configured Kani invocations complete.
24 PASS, 23 check failures,16 compiler failures,7 timeouts; these are
execution classifications, never closure counts. NCO_RESULTS.json and the
JSONL give every target/time/RSS/exit/revision. K048–K055 re-establish the
scalar contract/call-site/control packets with the complete pinset archived
by the stricter wrapper. K058 one-window expand contract PASS (64.38 s);
K059 inverted ensures FAIL (78.62 s), exact KMX source files checked.
K056 positive copy PASS and K057 wrong-copy FAIL in the same KMX configuration.

K060 full Result one-chunk validator TIMEOUT; K061 substituted caller PASS
has NO CREDIT because its callee contract was not proved. K062 inverted
validator and K063 weak validator TIMEOUT; K064 unimplied caller FAIL is
also only a diagnostic (no proved weak callee). No validator contract closes.
Generic Result<u8,u8> fidelity controls do pass, but they are not promoted to
an admitted arbitrary Error/slice/Vec contract family.

Borrowed result and Vec failures are compile-time missing Arbitrary support,
not desired assertion counterexamples. Result<&slice,u8> inverted and frame
controls K065/K067 fail and real-body K066 passes. Vec K068 wrong ensures /
K070 frame fail and K069 real-body passes, with exact KMX replacements;
Vec stub generation K016 fails. Neither family is admitted.

E006 includes the actual core::option::_::ok_or body. Unlike E005 it emits
no required external template. This removes that extraction gap without
adding an axiom or editing an existing module. The parser reference/model
equalities remain separate Lean obligations; no extraction success is called
a native bridge.

## Final Lean-side results before the audit

E006's Types/Funs compile in L011/L012; no unresolved external axiom is
imported. NCO_ParserShape L014 also connects row_shape to the exact
PrefixAggregate cohort used by the selected parser chain, not merely the
compact model. Rejection bridges L015/L019 and range rejection L024 preserve
nominal error mapping and input bytes within their printed hypotheses.

NCO_ValidateModel.reference (L058) proves the FULL extracted validate_ref
against LPl's actual kernel leaf (root r1_wire.validate_record_fields), every
payload length0..3712, all malformed bytes/tails, same first error row/index.
The proof uses checked addresses, a symbolic four-byte little-endian lemma,
one reference word step and two loop inductions, not116 concrete reductions.
NCO_CallerDomain.validator (L050) derives its cap from row_shape/framing and
the exact drop5 slice. This is model-to-model closure only; K060 did not prove
the frozen body contract. The distinct PrefixAggregate validator transport,
accepted parser cases and complete parse_at equality are still OPEN.

The general parse_at model composition draft remains failed (L059); its text
is excluded from accepted modules. It assumes a named lower reference equality
and never discharged it. It must not be treated as a native bridge.

Recommendation: **do not switch all lanes**. Retain the working pure-value
contract packets. Before a wider switch, obtain a checked borrowed/Vec return
mechanism with all per-shape controls, a full loop-leaf contract method under
the one-iteration rule, and enforce callee proof/control/domain closure in the
runner. Then repeat one complete vertical slice. Do not use raw-byte output
adapters, Option<fn> renaming, or a successful caller run under an unproved
contract as a substitute.

## Final audit and disposition

L060/NCO_Audit PASS: exit0, wall1.119898627 s, peakRSS2635468KiB,
swap0; exact source revision/hash/command and767 selected object pins in its
receipt. All52 explicit new top theorems have only standard axioms. Budgets:
70/70 Kani,60/60 Lean,6 extraction attempts. Final classifications and
per-proof times are NCO_RESULTS.json; no further proof was launched.

Postflight: all767 pins unchanged, no own process, own cache retained, own
Rust targets (about1.14GB) and temp directory removed; shared /tmp untouched.
Source audit:496 frozen paths,491 exact,3 cfg-only scratch changes,2 inherited
missing disabled client files. Shipped repository files did not change; ELF
pins are inherited, not reproduced. Full remaining native AND mathematical
obligations and exact next deliverables are in NCO_HANDOFF.md. The pilot does
not provide a complete vertical slice or establish the deployed100-bit target.
