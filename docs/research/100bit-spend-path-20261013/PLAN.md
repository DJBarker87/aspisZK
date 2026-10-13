# Transparent 100-bit spend path, 2026-10-13

Active goal: a private spend with at least 100 bits of security without credit for grinding, in one or at most two verification-and-settlement transactions. The user explicitly permits proof uploads outside this count and requires transparency/no trusted setup. Work lives on codex/100bit-spend-path-20261013, based on v8-reference 774295764.

## Evidence and scope

R0 has a substantial 32-round reference soundness development, including R0P.Mask.combined_fiat_shamir_masked; its coefficient is approximately 2^-105.136, with the explicit Qtot multiplier and oracle collision term. This is not a bound of 2^-100 for arbitrarily many queries. Privacy still requires MaskImageOn Good, including the spanning and witness-difference image obligations recorded in D19. No source theorem or experimental acceptance is substituted for these obligations.

The R0 15.08M and R1 S1/S2 6.77M/4.85M CU experiments are real failures for those binaries. P2's proposed 2.6M arithmetic floor is an estimate, not a proved lower bound against every implementation. The old wide-field screen explicitly states its generic kernel ratios are not lower bounds for specialized kernels. We will not treat either as a proof that transparent two-transaction spends are impossible.

## First bounded experiment

Import the isolated R1 P2 probe from d2197e355. Preserve the protocol, committed bytes, challenges, acceptance checks, and existing test fixtures. Test implementation changes separately from cryptographic redesign:

1. Inline WideExact scalar kernels to avoid unnecessary cross-crate aggregate-return/copy overhead. All canonicalization checks remain.
2. Replace the wide sampler's binary long division with exact base-P digit division. Ordinary sampling keeps the low eight digits. Gamma uses P^8 = 1 modulo P^8-1. Check equality against the frozen core sampler, including modulus boundaries.
3. Record the new SBF phase costs on the NUC using the existing proof fixtures. Compare exact native check traces and rejection behavior. Any stack regression must be fixed before accepting runtime data.

Time is expected in SBF compilation, then short release LiteSVM execution. No proof generation, elimination, full Lean manifest or public-network transaction is needed for this experiment. Each host build/run receives MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0; inspect reservations before launch. Retain keys; do not clean up or read key contents into logs. Freeze command, source revision/diff hash, elapsed time, RSS, cgroup peak and swap, ELF and input hashes. The old fixtures are immutable.

This is an implementation experiment on an unproved R1 protocol. A fit result would reopen a path; it would not establish soundness, privacy, account lifecycle security, or release readiness. The final path must account for settlement and checkpoint overhead within 1.4M CU per transaction.
