# Wide parser inline experiment: local SVM cost gate

This cost gate used the inline candidate ELF from the paired SBF bundle and the existing full-OS proof/public fixture. Proof SHA-256: `86d4212e675b36ebd556ca2b08b1b5e554cae15e77dfcd74c93a6f419129ed7c`; public fixture SHA-256: `f6bcd49446f1077d2c5ed4be940e91f0be444efc5ae83024ec0700b8c205c331`.

The historical local SVM gate ran 13 pairs, transaction version v0, using `--reuse` with the same proof fixture. It failed at stage 1 with `ComputationalBudgetExceeded` (exit 1). The trace reaches query 10 with 12,488 CU remaining, then reports program consumption of 1,399,494 out of 1,399,550 CU. No stage 2 or settlement result was produced. The raw run JSON, logs, input pins, and resource receipt are in `results/`.

This is a failed isolated performance experiment; it does not change runtime source or establish a full transaction result.
