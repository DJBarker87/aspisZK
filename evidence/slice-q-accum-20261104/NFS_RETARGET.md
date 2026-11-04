# Accumulation dependency diagnosis

Target not yet established. No ledger row is promoted by this diagnosis.

The complete import graph is stored once in NFS_SOURCE_GRAPH.json. NFS_DIAGNOSIS.json lists every module lying on a path from NEV_AccumPacket to S1SemanticPhaseV1, in dependency order, and each existing NFN owner. The field path is NEV_AccumPacket → NEV_AccumulateComplete → NEV_TailModel → NEV_PrimitiveTotal → NEV_PrimitiveBindings → NEV_StageWideFields → NEV_StageFields → NEV_MaskQM → NEV_MaskCarriers → NBG_FieldDischarge → LPi/LPf → FIo_NativeFuns → FIo_NativeExternal → FIo_NativeTypes → NP6_StdModel → ClaimsUnrolledFinish → S1SemanticFinishBoundsV1 → S1SemanticFinishModelV1 → S1SemanticPrefixModelV1 → S1SemanticPhaseV1. Other paths through emitted accumulation callees and prefix products are explicitly retained in the graph.

Reuse NFN_GeometryPart02's LPf_ReductionWord/CoreReduction/BaseMultiply and LPi_Total/NatBase/CMProduct/FieldValues; NFN_GeometryPart05's NBS_GeometryDomains; canonical RPz7 FIo objects and RPt/RPu adapters. NFN_PhaseTransport is imported unchanged. No legacy Phase module is copied, edited or redefined.

NFS_generate.py deterministically creates only the remaining 39 dependency modules, using the same namespace/import retarget method as NFN. Original bodies and hashes, maps and transformed hashes are recorded in NFS_RETARGET_PROVENANCE.json. Generated emitted function namespaces remain unchanged; proof namespaces receive NFS_. Every theorem in each new module is enumerated for #print axioms. Regeneration check compares exact bytes. Compilation and combined audit remain pending.

No crates/programs, ELF, protocol parameter, security metric, trust item or key changed. Prepared/powers/prepare remain out-of-slice boundaries. Cache setup validates NFP and NFN export hashes and copies inputs into the owned retained cache, with imported hashes in NFS_CACHE_IMPORTS.json.xz. No seed cache is modified.
