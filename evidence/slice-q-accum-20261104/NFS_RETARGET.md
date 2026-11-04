# Accumulation dependency diagnosis

Target not yet established. No ledger row is promoted by this diagnosis.

The complete import graph is stored once in NFS_SOURCE_GRAPH.json. NFS_DIAGNOSIS.json lists every module lying on a path from NEV_AccumPacket to S1SemanticPhaseV1, in dependency order, and each existing NFN owner. The field path is NEV_AccumPacket → NEV_AccumulateComplete → NEV_TailModel → NEV_PrimitiveTotal → NEV_PrimitiveBindings → NEV_StageWideFields → NEV_StageFields → NEV_MaskQM → NEV_MaskCarriers → NBG_FieldDischarge → LPi/LPf → FIo_NativeFuns → FIo_NativeExternal → FIo_NativeTypes → NP6_StdModel → ClaimsUnrolledFinish → S1SemanticFinishBoundsV1 → S1SemanticFinishModelV1 → S1SemanticPrefixModelV1 → S1SemanticPhaseV1. Other paths through emitted accumulation callees and prefix products are explicitly retained in the graph.

Reuse NFN_GeometryPart02's LPf_ReductionWord/CoreReduction/BaseMultiply and LPi_Total/NatBase/CMProduct/FieldValues; NFN_GeometryPart05's NBS_GeometryDomains; canonical RPz7 FIo objects and RPt/RPu adapters. NFN_PhaseTransport is imported unchanged. No legacy Phase module is copied, edited or redefined.

NFS_generate.py deterministically creates only the remaining 39 dependency modules, using the same namespace/import retarget method as NFN. Original bodies and hashes, maps and transformed hashes are recorded in NFS_RETARGET_PROVENANCE.json. Generated emitted function namespaces remain unchanged; proof namespaces receive NFS_. Every theorem in each new module is enumerated for #print axioms. Regeneration check compares exact bytes. Compilation and combined audit remain pending.

No crates/programs, ELF, protocol parameter, security metric, trust item or key changed. Prepared/powers/prepare remain out-of-slice boundaries. Cache setup validates NFP and NFN export hashes and copies inputs into the owned retained cache, with imported hashes in NFS_CACHE_IMPORTS.json.xz. No seed cache is modified.

## Focused replay

NFS_L001–039 replay every remaining module individually in dependency order. All exit 0, under -M7000 and 6G/8G/swap0/tasks64; no timeout, memory kill or rejected proof shape. Full section-6 fields, source/dependency/Aeneas hashes and theorem axiom lines are in NFS_ATTEMPTS.jsonl and per-attempt receipts. All printed axioms are standard. NFS_L039 checks the complete accumulation packet. This establishes focused retarget correctness, pending joint coherence and raw ax2 audit; no row promotion yet.

## Joint correction and accepted closure

L040 found an omitted owned-cache search directory (NFI exports); the own runner was repaired. L041 then found the legacy PreparedFromQmSourceBridge owner through NEV_CodeFieldBridge → NBG_Embedding → S1M31EmbeddingTotalV1. L042 enumerates the actually loaded graph. The canonical RPz7_S1M31EmbeddingTotalV1 has byte-identical non-import source (NFS_CANONICAL_EMBEDDING.json). The generator now also retargets NBG_Embedding and NEV_CodeFieldBridge, reusing that canonical object. The resulting 41 modules are replayed in three dependency-ordered compilation units at L043–045. Previous individual-module receipts remain preliminary, not the final selected objects.

L046 jointly imports the complete accumulation packet, RPx_Deployed, NFM, NFG, NFN geometry and all 26 accepted NFP modules: exit0,3.343479s,5830692KiB RSS,swap0. L047–054 build the unchanged-action ax2 driver, reproduce all eight fixtures, and raw-walk 12 selected accumulation/headline/support roots. Every raw walk is standard-only and agrees with collectAxioms. L055's strengthened scan returns zero dangling references, incompatible owners and independent-import mismatches. Raw scan and graphs, source hashes, driver diff, Aeneas/object pins and complete section-6 receipts are retained. This is cached coherent development validation, not a cold release replay or a query row closure.
