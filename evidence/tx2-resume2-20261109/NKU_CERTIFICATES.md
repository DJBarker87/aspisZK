# NKU native cut transcriptions

Target not yet established. NKK positives/controls are inherited, unchanged; no NKU Kani attempt yet. Source inputs are pinned by NKU_INPUT_PINS.json.

NKU_HeaderValue.value transcribes NKK_parent::header / header_prefix_stage, NKK_K028 positive, K029/K030 failing controls. Exact assertions: scanned == expected; out.is_ok() == entered && !nonzero; Err == Error::Checkpoint. Guards are len1768, magic R1P2CKP2, tag2, next<=22, flag1; reserved iterator is the actual bytes[11..16]. The complete iterator model and frame are NJJ_Any.installed/frame. NKU_HeaderStep.run writes only decoded next/end and phase in the one state; all other fields structurally retained. NKU_HeaderStep.source installs it before the actual afterHeader continuation; it is not yet a native parent certificate.

This is reviewed native contract semantic transport, reclassification under existing option-A P6/D188 trust, not removal or new trust. NKK_KMX patch unchanged, sha256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. No wider native caller domain inferred from a source equality.


The full native components are pinned in NKU_NATIVE_CUT_TABLE.json, with each positive, matched controls and actual source hashes. Source assertion blocks are evidence/tx2-resume-20261108/NKK_native.patch (SHA in NKU_INPUT_PINS.json). Their exact asserted pre/post domains remain in NKK_NATIVE_CERTIFICATES.json; no native-domain widening is claimed.

| Native component | NKU installed G/state assignment | SAME-argument source theorem |
|---|---|---|
| header_prefix_stage + NJJ any | NKU_HeaderValue/Step, exact guards then decoded next/end | NKU_HeaderStep.source |
| proof/public/checkpoint digest cuts | NKU_DigestProof/Public/Checkpoint, exact stored/chunk views, full immutable frame | NKU_DigestJoin.source |
| state_roots_stage | NKU_FineRoots, three single raw32 writes of decoded roots/Reader | NKU_FineRoots.installed + NKU_BodyJoin.source |
| gamma_stage | NKU_FineGamma, four single E writes and rho K, full Reader each time | NKU_FineGamma.installed + NKU_GammaJoin.source |
| query_chunk8/6 | NKU_FineWords induction + First/Mid/End windows; one raw4 write per occurrence | NKU_QueryFirst/Middle/LastJoin.source |
| semantic_writeback_stage + CLOSED semantic | NKU_Semantic, full10 array and cursor, prior frame | NKU_SemanticJoin.source |
| z_claim_stage | NKU_FineZ, four K then two E then K writes into SAME decoded record | NKU_FineZ.installed + NKU_ZJoin.source |
| SAME reservation/filled + CLOSED weights | NKU_Allocation/Weights, actual allocated owner carried as State.owned | NKU_AfterZ.source |
| owned_tail_stage + pair_owned_window + NJJ constructors | NKU_Tail full record, cursor rejection and actual Box/tuple moves | NKU_TailSource.source + NKU_AfterZ.source |

Representative exact assertions retained by the table: header scanned==expected and out.is_ok()==entered&&!nonzero; digest calls==1 plus exact seen_ptr/seen_len/seen_byte and checkpoint literal/prefix; tail error's dropped/ptr/len/cap and successful SAME owner/cell; pair weights/rhs/power/next and allocation frame. pair_owned_window alone observes only Prepared.variant; full Prepared value is supplied by the already retained NJJ PreparedCut field assertions and prepared theorem, not invented from K045. Error cleanup is the actual native Drop-site cut and child owned-weight error frame; aborts have no suffix by NKU_Chronology/NJJ/NJR retained laws.

All new parent-state assignments are pure field writes transcribing those asserted staged values, not additional opaque replies. Atomic read updates are NKU_FineRead; source/body equality fixes site and arguments. This is option-A P6/D188 reviewed-transcription composition, not new cryptographic or runtime trust. No multiplication stub, copy stub, writable static, Option<fn> or function-pointer verdict is introduced.
