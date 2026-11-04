# Reused Lean-discharged field stubs

No new Kani stub or multiplication check is introduced. The exact inherited tables are pinned in NFS_REUSED_INPUTS.json: slice-q-values NFP LPh_STUBS.md and its NFM/NEI/NEV references. All native caller inputs are established on the SAME query packet.

| Native stub/model use | Paired emitted Lean law in selected canonical closure | Domain derived here |
|---|---|---|
| NFP scalar node product | NFP_ProductLaw.emitted; NFP_NodeDictionary.product/node | all u32 products; geometry supplies canonical z; double/sub operands are returned canonical products |
| NEV accumulation wide product | NFS_NEV_PrimitiveBindings.product/product_returns; NFS_NEV_StageWideFields.product | actual line output via NFS_AccumDomain.line, actual a.power via NFS_QueryInvariant.active |
| NEV accumulation QM31 product | NFS_NEV_PrimitiveBindings.power; NFS_NEV_PrimitiveTotal.power | same a.power and p.rho from the root invariant |
| NEI circle/line field products and mul_m31/mul_by_r | NFS_NEI_FieldScalar/FieldCM/FieldQM/FieldWide copied laws; emitted/probe equalities are selected as RPu_JFv_RawExtractedSemanticCallOpsV20 | NFS_CallerDomains.folds derives both native fold domains from the same head/front execution and the actual field returns; inverses unrestricted by those child packets |
| NFM four-dot product windows | NFM_ProductInstance.main_law/tail_law and inherited wrapping-product bridge | SAME g29 canonical input and SAME original q opening, NFS_DotTrace.head and NFP_DotDomains.returned |

Field multiplication is never proved in Kani. The original stub sources, exact natural-number specifications, domains and failing controls remain pinned by their original tables and native validation; this table records the caller installations and canonical namespace retarget, not a replacement specification. P6/D188 native semantic transport remains option-A trust reclassification.
