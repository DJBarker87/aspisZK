# Isolated proof-extraction source changes: measured CU comparison

The research production measurement remains stage-1 max 1,199,687 CU and actual Pool settlement max 1,188,496 CU. The indexed source candidate at 5c63b0bba adds exactly 73,822 CU to stage 1 on each of six retained fixtures. Adding only #[inline(always)] to decode_k_value at de42cba00 recovers 29,147 CU on each fixture. It leaves an increase of 44,675 CU, with stage-1 maximum 1,244,362 CU. Settlement is unchanged. Neither candidate has been merged into research; no cryptographic parameters were changed for these comparisons.

| Fixture | Production stage 1 | Indexed stage 1 | Inline stage 1 | Settlement, both candidates |
|---|---:|---:|---:|---:|
| transfer-13 | 1,199,648 | 1,273,470 | 1,244,323 | 1,137,397 |
| transfer-255 | 1,199,567 | 1,273,389 | 1,244,242 | 1,174,671 |
| transfer-1023 | 1,199,687 | 1,273,509 | 1,244,362 | 1,171,579 |
| withdrawal-13 | 1,198,225 | 1,272,047 | 1,242,900 | 1,150,958 |
| withdrawal-255 | 1,198,264 | 1,272,086 | 1,242,939 | 1,188,496 |
| withdrawal-1023 | 1,198,386 | 1,272,208 | 1,243,061 | 1,185,236 |

The inline candidate's executed stripped artifact is 320e156d1e4e17ba9f0249cc93558a3aa07402aef7e6a2ac61b35e6e228b778c. Its linked artifact is c9ba71c3c6211bfc93d71d1e11de3f372cb3149b549f1bf36db855029ea3e330; the strict stack check passed and verifies executable-section identity between linked and stripped artifacts. Its SBF build exited 0 in 5.504 seconds with peak process RSS 232,956 KiB and zero swaps. All six runtime comparisons accepted, with byte-identical proof hashes to the corresponding first candidate and unchanged settlement CU. Every new job used a separately admitted 6 GiB high / 8 GiB maximum / zero-swap scope; commands, reservations, receipts and complete runtime JSON are retained.

The first indexed candidate's native core/checkpoint/codec/ordered-hash checks are retained with their actual attempt receipts, including unsuccessful diagnostic attempts. They must not be described as newly run checks of the inline artifact. The runtime fixtures are explicitly reused; their mask entropy is not established by this comparison. Full-random-mask measurements, candidate injection gates, complete source equivalence and a universal CU upper bound remain open. The inline candidate still misses the 1.2M measurement target. Inlining identifies one code-generation contribution; the remainder of the source changes has not been individually attributed.

Only allowlisted commands, receipts, public runtime results, trace output and stack reports were copied from the NUC. Task directories, account keys, source workspaces and executable binaries were excluded. Existing task keys remain securely retained on the NUC. This packet is measurement evidence, not the complete private-spend soundness/privacy theorem or a deployment result.
