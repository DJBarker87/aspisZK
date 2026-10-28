# NCO parser slice bridge matrix

Primary vertical slice: `parse_record_at → parse_record → row_shape / validate_record_fields`.
These are real frozen call dependencies (F152→F151/F153; F151→F153/F154).
The inherited LPl validation leaf is historically CLOSED on length≤3712; the
pilot does not promote that certificate to an automatically proved Kani contract.
The complete unit-10 inventory is retained below so no member is silently closed.

|Function|Native contract / control evidence|Extracted-reference equality / remaining work|Caller domain|
|---|---|---|---|
|F153 row_shape|K048 PFC PASS; K049 stub caller PASS; K050 wrong caller and K051 inverted ensures FAIL|E004/E006; NCO_ScalarBridge.row_shape, NCO_ParserShape.prefix_shape/parser_shape/source_shape, standard axioms|ALL u8; exact Option tag and size, including None|
|F097 compact_row|K052 PFC / K053 caller PASS; K054/K055 controls FAIL|E004, NCO_ScalarBridge.compact_row|ALL u8; exact Bool|
|F154 validate_record_fields|K060 body, K062 inverted, K063 weak body TIMEOUT. K061 caller PASS is conditional on an UNPROVED contract; NO native credit. K064 is a diagnostic failure under the unproved weak contract.|E006, NCO_ValidateModel.reference (L058) proves complete Result/error-index equality after explicit RefError mapping to the LPl carrier. Exact kernel target is ROOT r1_wire.validate_record_fields from LPl_Kit_FunsExternal; carrier LPl_Kit_Release.r1_wire.Error. This is not a theorem about the distinct PrefixAggregate validator.|Reference domain: every row, payload length0..3712, all bytes and tails. Diagnostic Kani domain32 is insufficient at row25. NCO_CallerDomain.validator derives the full reference cap from shape/framing/slice facts.|
|F151 parse_record|K038 general restricted-class, K043 header≤5, K045 status-only header, K047 exact row2/len37 TIMEOUT. K039 borrowed-result stub compiler rejection.|E006 compiles; NCO_Framing.invalid_bridge / length_bridge prove rejected-row and wrong-length branches against AspisR1PrefixAggregateParser.r1_wire.parse_record. Accepted/tag/header/validator transport remains OPEN.|Kani row<14/len≤37 restrictions exclude real row25: explicit finding, never an adopted contract. Reference partial-branch hypotheses are printed in source.|
|F152 parse_record_at|K044 actual caller under stub_verified(parse_record) rejects returned &[u8] generation; no composed credit.|E006 compiles. NCO_ParserAt.reference_short/source_short prove the exact range-get None branch. General caller model composition draft fails in L053/L055/L057/L059 and is retained ONLY as text. No callee-equality hypothesis is claimed discharged.|Valid row shape and checked sums; range-get equation is an explicit mathematical premise of the partial short-branch lemmas. Full caller establishes/proves these domains still OPEN.|
|F099 expand_values|K058 PFC PASS (16→32 one window), K059 inverted ensures FAIL; K056/K057 KMX copy positive/control. No full-domain contract or stub call-site proof.|Existing LPn symbolic spatial/frame/induction evidence is reused as context only; new expanded_one predicate has no extracted functional-reference equality. Full leaf contract remains OPEN.|Only16/32 in pilot; actual row25 uses1856/3712. NCO_Domains gives concrete contradiction to treating this as the full caller domain.|
|F098 expand_semantic|Not attempted as a whole-buffer loop, per loop ruling; no full-domain expansion callee contract available.|Existing S1NativeCompact model remains; complete new f_ref equality absent.|One native row iteration + closed whole callee contract/domain association required; never assume the final buffer equality.|
|F100 slot_offset|No native one-step contract; no credit.|E002 fails at reference array access, InterpBorrows.ml:2731. No slot reference was emitted by E003/E004.|slot0..6; next work: proof-friendly safe reference and extracted loop invariant, then native iteration.|
|F138 Prefix::parse|No composed native contract; blocked behind parse_record_at and borrowed/aggregate returns.|No new complete reference equality.|Same complete Prefix, ordered27 rows, exact exhaustion; no top success assumption.|
|F139 Prefix::payload|No native contract; returned borrowed slice shape unsupported in K011/K014 and actual K044.|Inventory has no direct cohort counterpart; requires record/subslice model composition.|Parsed Prefix token, same framed bytes, len≥5.|
|F140 Prefix::record|No native contract; borrowed Result substitution unsupported.|No new f_ref equality.|Same Prefix, row<27 on success; exact InvalidRow otherwise.|
|F141 Prefix::validated_record|No native contract; borrowed aggregate interface not admitted.|No new f_ref equality.|Same token, row and frame returned by record; cannot independently select them.|
|F148 ValidatedRecord::framed|No native contract; borrowed output barrier.|No new f_ref equality.|Same live validated token and backing.|
|F149 ValidatedRecord::row|No native contract; independent scalar member remains for a fresh Kani allocation.|No new reference extraction/equality. Outside the selected vertical chain.|Actual token row; cannot turn this isolated getter into parser closure.|

Kani contracts compose only when the matched callee body proof and controls are
closed on the caller-established domain. `stub_verified` does not itself check
the callee's previous run succeeded. Every unproved use above stays OPEN.
No XRn join kit or stand-in, field-multiply stub, SHA implementation, observer
function pointer, shipped-source edit or headline-premise removal is used.
