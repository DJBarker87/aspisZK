# Lead review: R1 on Solana devnet (2026-10-20)

Reviewed: cx-devnet3 (9 commits through 0227fb4a5),
`evidence/devnet-r1-20261020/` (REPORT.md, README.md, signatures.json,
receipts/). The lead read one settlement transaction back from devnet RPC
(finalized, no error) before accepting.

## Result

The frozen R1 verifier (devnet-id build fb2fc048…, `.text` identical to the
frozen default dfc2a91a…), the Pool (121f3e29…) and the registry were
deployed at the reserved devnet ids; a pool, lanes, pages, a devnet mint and
vault were initialised; a note was deposited; a private transfer and a
withdrawal were each proved with the retrying prover (P_R1 on), uploaded in
16 + 1 TxV1 chunks, verified in stage 1 and settled in stage 2.

| Phase | Transfer | Withdrawal |
|---|---:|---:|
| Prove (P_R1 on) | 37.1 s | 37.0 s |
| Uploads (16 + 1) | 7,385 CU total, ~258 s incl. HTTP-429 recovery | 7,385 CU, 58.7 s |
| Stage 1 | 1,197,994 CU, 3.3 s | 1,195,252 CU, 5.4 s |
| Pool settlement | 1,135,083 CU, 5.3 s | 1,146,410 CU, 5.3 s |

Settlement state read back: vault 1,750 base units, destination 250.
Negative checks (four) finalised as rejections: tx2 replay as consumed, a
mutated proof byte at stage 1. All CU figures are inside the frozen bound
(`LEAD-REVIEW-CU-BOUND-4-20261020.md`). A config-driven driver repeats the
spend (README commands); 26 devnet-only keys and the note-recovery files
stay on the host, none committed.

## Reading

This is the first R1 execution on a public cluster. It is a measurement and
a demonstration, not a security claim: the soundness theorem is open on the
gap-map items, and the deployed devnet programs are not a release. The
upload phase, not verification, dominates wall time; the transfer's 258 s
is mostly RPC rate-limit back-off and is a client-pacing matter.
Demo go/no-go for 5 November: GO on the R1 path.
