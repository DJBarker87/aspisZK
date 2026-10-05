# R935: complete ordinary independent-output observation law

For every starting transcript state and every rational-valued observation of the ordinary sampler output, proves the exact independent-answer mean: the explicit failure mass times the observation of failure, plus the common canonical tuple mass times the sum of observations of all canonical four-tuples. Canonical support is proved through the existing finite-block execution law. The error-zero specialization evaluates the failure term; it does not condition on success. This is an output marginal law, not a return-state independence or complete callback trace theorem.

Target `AspisV8R19/R935OrdinaryObservationLaw.lean`; source revision `a0db028bcd318389e0489a138acb00b7d5ff7d02`; SHA256 `bfc21858cd39e12e65e30792b79aebb11d925201021ae5ea8f901ab7c1d64871`. Exit0; wall 0:01.46; peak Lean-child RSS 3280500KiB; swap0. Pinned Lean4.32 cached workspace, -j1 -M4500, own5G/7G/swap0/TasksMax128 scope. All 10 complete axiom reports use only standard propext/Classical.choice/Quot.sound or subsets. Exact successful source, full log, receipt and runner are saved, along with every listed rejected attempt. No unchanged successful check was repeated.

First remaining proposition: Instantiate the adaptive stage bounds using these complete output laws, preserving callbacks and failure, then connect the actual shared-oracle execution and account for its losses.

Verifier results999,790/999,532CU and all security parameters unchanged. No native execution, full privacy, shared-oracle law, published-view simulation, probability loss or soundness claim follows beyond the stated proved boundary.
