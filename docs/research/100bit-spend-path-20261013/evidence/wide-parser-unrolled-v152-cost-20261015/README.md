# Unrolled wide parser candidate: local SVM cost and settlement gate

The isolated candidate ELF (`ea9be844a7027f613cf310c5fedd54c8db9e6d669ba325af46d3b5908ef43796`) was tested with the existing 13-pair, v0 transfer gate and the same full-OS proof/public fixture used by the other v1.52 comparisons. Proof SHA-256: `86d4212e675b36ebd556ca2b08b1b5e554cae15e77dfcd74c93a6f419129ed7c`; public fixture SHA-256: `f6bcd49446f1077d2c5ed4be940e91f0be444efc5ae83024ec0700b8c205c331`.

The local LiteSVM scenario completed with `outcome: accepted`. Stage 1 used 1,392,386 CU and a 295-byte transaction. The transfer used 1,303,475 CU and 879 serialized bytes against the 1,232-byte target (353 bytes of headroom). Simulation and execution matched; the evidence records the expected state changes and selected verifier CPI. This is local cost/settlement evidence for the unproved R1 cost-probe path, not a semantic proof or deployment claim.

Raw driver/resource logs, evidence JSON, fixture bytes, and input hashes are in `results/`. Task keypairs are retained remotely and in the local private retention directory outside the worktree; no key contents are included here.
