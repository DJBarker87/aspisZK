# NJE opaque boundaries and Lean laws

P6/D188 option A reclassification; no trust added/removed. No field multiplication runs in Kani. All imported NJA field logs remain paired with their emitted laws in NJA_STUBS.md. Fresh NJE native harnesses introduce no field-product stub.

| Boundary | SAME-call law | Domain |
|---|---|---|
| NJA_product, pow5 calls | NJE_Residue.multiply; NJE_Pow5Packet.laws/TX1_307; NJA_FieldLaws.generated_mul | Canonical M31 input, each returned word canonical; next operands exactly preceding replies, domain derived by NJA_Pow5Cut.caller_domains |
| NJA_reduce, matrix/linear calls | NJA_FieldLaws.reduce_u62; NJE_Residue.value/canonical; NJE_Mat4Packet.laws/domains; NJE_InternalPacket.result | SAME u64 argument <2^62 proved from canonical original cells, preserved sum and native frame; canonical replies derived |
| NJE_order_all | NJE_AllAdapter.default_all; NJE_WellSource.order_all; NJA_WellPredicateLaws.order | SAME immutable u32 slice, windows2; native full headers/predicates K085..K096; list induction; no external state/effects |
| NJE_domain_all | NJE_AllAdapter.default_all; NJE_WellSource.domain_all; NJA_WellPredicateLaws.domain | SAME immutable u32 slice, strict <2^18; native header/predicate laws, every callback unit state |
| NJE_group | NJE_CountGroup.total | SAME u32[16], i<n<=16, sorted unread suffix; exact parent at i shifted one bit. Inner loop is pure; q-i in1..2 must be derived, never a caller-success premise |
| NJA_digest local record | AspisR1.NGC_DigestBridge.forwarding; NJE_ParentPackets.TX1_123/TX2_089/TX1_125/TX2_091 | SAME deployed SolanaDigest, tag18, exact ordered child32 slices; reply unchanged. Digest value remains existing RuntimeSyscall/SHA realization; runtime abort is terminal prefix |

NJE_group and the two all boundaries have no new row credit until their native pairs and full loop/source certificates pass. No runtime totality is inferred. Default-all ABI adapter is the existing NFU_LPl_Kit_FunsExternal body on canonical Aeneas types; no shared library object is replaced. KMX is byte-identical to the mandated patch; no custom copy stub.
