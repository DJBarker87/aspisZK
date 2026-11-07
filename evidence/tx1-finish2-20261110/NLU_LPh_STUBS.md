# NLU opaque arithmetic and copy table

No field multiplication/addition implementation is evaluated in Kani. K023/K024 check the LOCAL opaque three-call operand/order/reply log. Replies are independently arbitrary there and are instantiated in Lean with the SAME emitted values by NLU_Arithmetic.source. This is component support, not full136 closure.

| Call | Frozen operation | Named paired Lean theorem / domain | Parent status |
|---|---|---|---|
|0|QM31.mul(eta,terminal)|AspisR1.NLU_Generated.emitted_mul proves the actual emitted definition returns ok with canonical exact decoded product, using generated_qm_mul_eq_probe. AspisR1.NLU_FieldValues.mul_value transports the same law to fixed deployed boundaries. Both operands canonical.|eta own-input clause; SAME256 output canonicality proved in NLU_Terminal.source; actual parent slot integration OPEN|
|1|QM31.add(mask,product)|AspisR1.NLU_FieldValues.add_value, from existing NJB_StubLaws.qm_add and emitted/probe transport. Canon both operands; product canonicality derived internally.|mask from actual CLOSED TX1:076 NHU_Mask.result, not147; full source/native parent slot association OPEN|
|2|QM31.add(partial,extra28)|Same add_value law. Canon partial from call1; Canon extra28 from SAME decoded25 value.|147 is decode_k; exact row25/29/87 domain derived in NLU_Decode.source; full parent value/cut integration OPEN|
|copy_nonoverlapping|Exact KMX_copy_stubs.patch|Exact patch/source hashes in NLU_INPUT_PINS, source pins and each native gate. Paired arbitrary-offset controls and existing KMX value/frame laws.|per-member support; no full-parent heap claim|

NLU_FieldValues and NLU_GeneratedMul have focused successful standard-axiom receipts. NLU_Arithmetic instantiates all three value laws and logs internally at SAME original/intermediate operands. Canonicality of its segment inputs is an explicit helper domain, not an allowed leftover136 root premise. It must be derived from the parent state before a136 root could use the segment. No unpaired field stub is claimed a pass, no new axiom/trust row is introduced, and eligible transport remains existing option-A P6/D188 reclassification.
