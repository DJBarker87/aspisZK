# Native stub, law and domain table

All native credit is local/partial as itemized in NIC_CLOSED.json. No trust row is removed; native semantic transport is the retained P6/D188 option-A reclassification. No native field multiplication is verified by Kani.

| Stub | Exact named Lean value law | Domain / installation |
|---|---|---|
| m31_product_spec | NIC_FieldStubs.m31 / NFP_ProductLaw.emitted | all U32 pairs; returned M31 is exactly natural product mod P, canonical |
| wide_product_spec | NIC_FieldStubs.product / NFS_LPi_TowerValues.wide_mul | canonical eight-word operands; native inputs generated canonical; dependent fold domains proved in NIC_FoldDomains, physical full-fold association still OPEN |
| wide_add_spec | NIC_FieldStubs.add | canonical eight-word operands; exact componentwise natural mod-P sum |
| q_subtract_spec | NIC_FieldStubs.subtract / NFS_LPi_TowerValues.qm_sub | canonical four-word operands; exact componentwise natural mod-P subtraction |
| wide_scale_spec | NIC_FieldStubs.scale / NFS_NBG_FieldDischarge.wide_scale | exact componentwise product with scalar mod P; emitted law is total for raw inputs; caller E canonical for downstream additions |
| q_product_spec | NFS_LPi_TowerValues.qm_mul | canonical four-word operands; exact mulQ; native tail's power/rho canonical domain supplied by NFS invariant |
| wide_q_spec | NFS_NBG_FieldDischarge.wide_qm; NFS_NEV_StageWideFields.product | canonical E and Q; canonical Q makes the emitted normalization identity; exact pair of natural mulQ results |
| raw_product_spec | NFE_NEV_DotScalar.product; NFF_Cell.primitive_reply / NFM_ProductInstance.main_law | both U32 operands < P, asserted at each native call; the emitted widened checked product returns ok with EXACT a.val*b.val and <= (P-1)^2 |

Wide/Q natural references use the same Karatsuba formulas as the selected mulC/mulQ/mulE; CM real/imag words and exact widened-sum bounds are NFN_LPi_CMProduct.source/cross_value. Wrapping arithmetic in the reference therefore does not truncate on the stated canonical domain. K077 and K079 use independent scalar-limb equality constraints, avoiding the OWN reference's accidental 32-byte memcmp loop. Earlier whole-fold timeouts and undetermined/memcmp failures are excluded. No spec constraint is replaced by a successful result premise. Complete native caller-domain installation is not inferred from the total model laws.

Runtime frontier: SolanaDigest::digest; solana_program::hash::hashv; program::{set_return_data,get_return_data,invoke,invoke_signed}; log::{sol_log,sol_log_compute_units}. Every replacement asserts unreachability. Each event-kind control activates a digest; K021–K027 independently activate the other seven mappings. These are purity assertions, not replacement runtime values. No hidden syscall was found.

AbortDigest is a LOCAL Cell-record backend for the unchanged generic frozen transcript methods. It returns arbitrary32 until the selected abort, then terminates the path. NGT/NHK exact returning logs are reused; accepted RuntimeSyscall supplies returningValue with no totality. Downstream sampler/reduction stubs assert unreachability (they provide no values on a credited path). The typed Box::new abort stub likewise terminates; returning value/ownership are the reused NGN/NHS (aa) checks and the retained allocator row, not new allocation claims.

KMX is exactly KMX_copy_stubs.patch, sha256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67, unchanged. K017/K018 calibrate its copy/inverted-copy behavior in the same deployed program configuration. This lane asserts syscall absence/no-suffix, and claims no new copy value/frame refinement. All later reached copies use the exact annotation. Earlier independent absence checks are not replayed as new value checks.

No proof_for_contract/stub_verified, Option<fn> observation, writable static or new copy stub is introduced. Rules 14/16 quarantine no own result. NIC_REUSED_INPUTS.json pins reusable laws/packets; raw-source citations in NIC_RAW_LAW_PINS.json pin the exact retained emitted-product law. The remaining native domain finding is NIC-D1, documented without promotion.
