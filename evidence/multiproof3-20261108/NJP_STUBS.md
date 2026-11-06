# NJP stubs

K006/K007 are ruling-(ad) control-only. NJP_cell_control and NJP_linear_control record body visits and do not return arithmetic values or certify a field operation. They have no field-value credit, hence are not rule-A multiplication stubs. The value association reuses NJE_RoundComposition.cell_law, NJE_ExternalTotal.result, NJE_InternalRound.result and their named Lean-discharged field laws; exact per-stage source/native pins will be listed in NJP_CERTIFICATES.md before row proposal. The concrete |_| {} callback is retained and no function-pointer value is observed.

Copy builtins use exactly KMX_copy_stubs.patch sha256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. Each new copy-dependent claimed pair needs its semantic control; historical K005/K002 is support only. No writable static, stub_verified or new trust row.

| Native boundary | Paired emitted/model law | Established domain |
|---|---|---|
| Inherited NJA_product in pow5 | NJE_Residue.multiply; NJA_FieldLaws.generated_mul; NJE_RoundComposition.cell_law | M31 canonical at callers; generated multiplication equation is total on U32 words |
| Inherited NJA_reduce in matrix/external/internal layers | NJA_FieldLaws.reduce_u62; NJE_Mat4Packet.domains; NJE_ExternalTotal.result; NJE_InternalRound.result | SAME natural argument <2^62, derived for each current cell and canonical threaded state |
| NJP_permutation in compression caller | NJP_PermutationPacket.TX1_306 and model_domain | SAME full 16-limb seeded state; canonicality derived by NJP_CompressionPacket.child_domain |
| NJP row occupied/sibling raw digest reply | NJE_ParentPackets.TX1_123/TX2_089 and TX1_125/TX2_091 with NGC_DigestBridge.forwarding | SAME value array/index and selected physical sibling; readonly frame; raw digest byte[32] including every returned value, runtime abort uses (an) prefix |
| NJP_digest_write_record | Real NJP_digest_write_window plus NJP_CopyFrame.flat_window/outside/digest_write_ext | Arbitrary original full byte[16][32], target row<16 and byte<32; no field arithmetic |

Natural field values are installed by those named emitted laws during Lean composition, rather than verified as multiplication in Kani. Native arbitrary-reply stubs never supply an unproved successful endpoint to a root. The compression row remains conditional on admission of the permutation candidate at the next lead gate.

Final association: NJP_NativeCohortStep.observation pairs each row arbitrary reply
with NJP_RequestTransport.hash H at exactly NJP_NativeRowCut.request log.
NJP_CohortSupplied.available derives the full borrowed window from physical_read
and read32, without a <=5504 strengthening. The proof carries up to 9216 bytes.
NJP_CohortRowLoop.digest is a concrete total interpretation for proving the
cohort iteration invariant; it is not an added runtime trust item or a free
successful-child premise at an admitted root. No proof_for_contract/stub_verified
or interface-shape contract was used, and no function-pointer quarantine credit
is claimed. Runtime digest values retain the existing runtime trust row.
