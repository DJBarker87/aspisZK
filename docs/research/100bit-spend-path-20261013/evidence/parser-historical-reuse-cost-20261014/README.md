# Historical SBF P3 gate with reused proof

One capped local LiteSVM run used the historical P3 verifier artifact (`c94675…`) with the same pool, registry, proof, public bytes, pair count, and transaction version as the baseline control reuse gate. Stage one used 1,390,128 CU in a 295-byte transaction and passed. The terminal transfer used 1,293,571 CU in an 879-byte TxV0 and passed under the 1,400,000 CU limit, reaching `r1:final`. Settlement flags report the expected history, lane, and nullifier-marker updates, with checkpoint, entry, master, and registry unchanged. The previous full-OS fixture used the same public bytes but a different OS-generated proof (`f04b11…` vs `86d421…`); it recorded 1,390,049 CU / 295 bytes at stage one and 1,293,584 CU / 879 bytes at terminal: historical-minus-fixture deltas are +79 CU and -13 CU, with no serialized-size difference. These are comparisons between separate proof draws, not an identical-proof differential.

This is a local cost-path measurement for the historical verifier and a reused proof/public pair. The run used `--reuse`, so it did not draw a new proof or mask. It does not establish equivalence between the historical and newly built artifacts or prove the R1 protocol.

The capped resource receipt is `historical-reuse-run.json`; the full scenario result is `historical-reuse-evidence.json`; the human-readable gate output is `historical-reuse-run.log`. Inputs and output fixtures are hash-pinned in `input-pins.txt` and the manifest. Reused proof/public bytes are included in `task-artifacts/`.

The local LiteSVM invocation created task key files. They remain on NUC with mode 0600; secret contents were not copied or deleted. No network, signing service, or funded external account was used.

A first wrapper invocation used an incorrect recorder path and stopped before the driver ran; it is recorded in `setup-path-error.txt`. The successful invocation used the pinned recorder path and a separate cgroup scope.
