# NET field oracle obligations

Native multiplication never executes in the NET caller gates. Every log and
counter is a local owned record. `NET_STUBS.md` records the inverse frontier.
The inverse log certificates remain PARTIAL and receive no composed credit.

| Native oracle/call slot | Paired emitted Lean theorem | Domain and status |
|---|---|---|
| NET_fixed_backend product slots 0,1,4,6 | NET_MultiplyBridge.product and product_reply (NET_L008) | All raw U32 operands; exact ok natural product modulo2147483647, canonical reply. Source-fission model pairing only; inverse/neg child transport remains OPEN. |
| NET_QLog product slots | None newly claimed | OPEN: no whole inverse chain substitution is credited. |
| NET_prefix::NET_product | NEG_PrefixStep.multiply, NEI_PrefixWindows.specialize_field_reply | All raw U32 operands, exact emitted prefix M31 product and canonical reply. Native oracle accepts every raw reply, a superset of the exact result; active caller index establishes both operands. Imported theorem replay and complete prefix composition are pending. |

The prefix oracle imposes no stronger arithmetic precondition than the actual
callers establish: arbitrary raw inputs are admitted. Its Kani result covers
every reply and the paired Lean law selects the exact canonical one. This is
the approved opaque-call-log multiplication method, not a Kani multiplication
proof or an unpaired stub pass. Every nonproduct inverse slot without a closed
callee association stays explicitly OPEN.
