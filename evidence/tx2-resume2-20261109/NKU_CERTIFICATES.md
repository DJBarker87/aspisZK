# NKU native cut transcriptions

Target not yet established. NKK positives/controls are inherited, unchanged; no NKU Kani attempt yet. Source inputs are pinned by NKU_INPUT_PINS.json.

NKU_HeaderValue.value transcribes NKK_parent::header / header_prefix_stage, NKK_K028 positive, K029/K030 failing controls. Exact assertions: scanned == expected; out.is_ok() == entered && !nonzero; Err == Error::Checkpoint. Guards are len1768, magic R1P2CKP2, tag2, next<=22, flag1; reserved iterator is the actual bytes[11..16]. The complete iterator model and frame are NJJ_Any.installed/frame. NKU_HeaderStep.run writes only decoded next/end and phase in the one state; all other fields structurally retained. NKU_HeaderStep.source installs it before the actual afterHeader continuation; it is not yet a native parent certificate.

This is reviewed native contract semantic transport, reclassification under existing option-A P6/D188 trust, not removal or new trust. NKK_KMX patch unchanged, sha256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. No wider native caller domain inferred from a source equality.
