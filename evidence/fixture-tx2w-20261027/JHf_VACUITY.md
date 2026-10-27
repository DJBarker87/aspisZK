# Retained support images disagree with the target public statement

Target not yet established. This finding stops the claimed unconditional reconstruction/accepted2 item on the corrected JHb_World tuple; independent obligations continue. No fixture or security-contract change is adopted.

The frozen Rust identity decoder reads `deployment_domain` from identity[112,144); the master embeds that identity at [64,208), so the domain is master[176,208). The checkpoint decoder reads its domain from checkpoint[40,72). JHf_DomainBytes computes these exact retained windows. Both begin with byte0 and agree in all32 bytes. The retained target snapshot/public statement domain begins with byte5 (indeed all bytes5). Thus these are different domains, not alternative carriers of identical bytes.

`JHf_AuthenticationDomain.preserves` proves over the actual retained checked `JHd_Authentication.afterMaster` continuation that every successful returned authentication copies the supplied master's identity domain to the live snapshot. `JHf_ReconstructDomain.preserves` uses the existing exact extracted reconstruct success theorem and proves every successful reconstruction preserves that live domain. `cannot_match` proves that a live snapshot faithful to this master's decoded domain cannot reconstruct an output with the target domain. These facts have passing receipts and only standard axioms.

This does NOT prove that the abstract installed op48 actually decodes these bytes; that native/source association remains open. It proves incompatibility of the requested target success with faithful decoding/copying. Installing an arbitrary successful op48 or op52 would conceal this finding. It also does not refute the protocol or the universally conditional deployed theorem.

Required repair, for the lead to assess: supporting master[176,208) and forest-checkpoint[40,72) must agree with the fixed public domain, and all authentication/statement/PDA/source/native associations must be rechecked for the same tuple. Do not change the real proof/public/checkpoint bytes to hide the mismatch. No existing JHb_ file is edited by this worker.

## Exact target and generator diagnosis

JHf_ExactDomainObstruction.target_domain and cannot_reconstruct now pass on the explicit roundtrip-checked nominal transport of JGx_RealStatement.value into the actual extracted reconstruction types. No desired-output equality is assumed in cannot_reconstruct.

The supplementary-image generator supplies both domain fields from `pub[208:240]` (JHb_generate.py lines50 and52), while the actual retained snapshot domain is `pub[256:288]`, as fixed by JFu_PublicMeta03.selected. JHf_GENERATOR_FINDING.json pins the original generator. It is left unchanged. This explains the concrete bytes without attributing the issue to shipped Rust, proof/public generation, or the protocol.

## Stronger source result

Attempt064 proves the actual terminal validator returns `Err DeploymentBindingMismatch` on JHf_ReconstructedStatement.value: retained target fields/payment, with only the live domain faithfully copied from the retained master. It is a diagnostic copied-field value, not a fabricated successful authentication.

Attempt065 proves `JHf_NoReconstruction.source`: for the exact decoded/nominally transported real request, ANY candidate and ANY authenticated record with live domain equal to the retained master's domain, there is NO successful result of the actual extracted reconstruct_asq8_statement. It does not merely exclude the desired target. This uses the source validator's checked deployment-domain guard, full success inversion and complete request/carrier maps.

The specific faithful-domain condition is a necessary source-decoder field law; it is not asserted as an established native op48 result. An arbitrary op48/op52 model callback could evade it, but would not certify the actual source on these bytes. Full native/ELF and all headline-hypothesis non-vacuity remain unestablished.
