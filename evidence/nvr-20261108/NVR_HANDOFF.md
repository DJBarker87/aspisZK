NVR host handoff

Status: all 14 NVR draft modules compile byte-identically against the retained ledger29 rev4 selection. No row credit is claimed. Final combined coherence/audit results are recorded by NNO_HANDOFF.md.

Prepend `/home/dombarker/project-offloads/codex-cx-fin-host-20261108/NNO_exports` to the chain in `evidence/fin-host-20261108/NNO_PATHS.json`. This is a COPYING seed of ledger29, with job-owned compiled objects. Do not write into the retained source caches.

| Module | Old source SHA-256 | New source SHA-256 | Olean SHA-256 | Scope receipt |
|---|---|---|---|---|
| NVR_NoWritePool | eb12f8c79cbb4302e4e100ca987c2d2a77220246c727cc4939ff6f1cef40ed80 | e7051247174db29131d98651480ca1c9774bc3339eb7115323d6b807ad02448f | 1bad329ed23a61f3e336439ed8256d0b26a91bc97ddafd563a43dd1399d115bc | NNO_L001/receipt.json |
| NVR_NoWriteOwned | ce0792e7a798d38f8844550a571206c9ee4dac0ce00e5dd4f5e4532baf5c47ad | c1e0f2f8409253ae35493d056ea4bb9ece170171ba129717fec7d0fd30e73359 | 9d88871bd183e499514fa7579c6af1a475c0cc07f9c0d7bac8b35555e5522f4e | NNO_L002/receipt.json |
| NVR_NoWrite241 | 51ee068eef86f5d36357348b81a78db892aaba7b1c98443fb144ef29a02bbb99 | 5ebfd0c0691035c422db799cd08788bdfebbe994862555011c7a55ed3cb69d64 | ff824ee98d19d70adaae69c207f8a42931eb74ca9450ab2f8166fd0bd906b266 | NNO_L003/receipt.json |
| NVR_G2Reference | b0c1f970373368906ba5117fed7eab3ce83f5f2fd902e60166b411d4c2936ee4 | db20bfe08ca17e938acc1000d16f4eac4f9be961ef0968b1a335fbdb8841687f | fb2f065df69a3897af0fe85130f364424b8cb5b71c2fb3db97da0fd822c9c377 | NNO_L004/receipt.json |
| NVR_TasRoots | 6595a2baf5d394d3c91f4a3b7b58803a4c26396c8330ff27d9c2928b6c4710d3 | 58f581b811566fbd39373a2fbf36e7b35c853d2f75fb22f2efc3c8ead951ef5b | 4d74fdc3c76a3ad6a8b2b58a274f458bfed133de85e12c21fcfadb1c4240447e | NNO_L005/receipt.json |
| NVR_CandidateRoots | 94fe10f680bcc85e787a4eee314662f36499e36734bc18e880eab74a15841aa7 | 69eb9b1cbd9bab25265fa8547e54fac4df78b38473167db5868a37be1d0aa78a | 5574e4717f492f281971aaf36dc4370b61ee58ac3a3a12439e3bbbced917db0a | NNO_L006/receipt.json |
| NVR_Carrier | a943befdae54d801942c7b577301f36e4d731307e1619954530a26363bb1add9 | 8b4d16b93c86051ca5edf596eaec8a24e96e77a5a534409d5c34cefa502372e8 | f931c72001af65eaa7d812c74185ac9eec4e1489d1ec84b6220fc5563d861ebf | NNO_L007/receipt.json |
| NVR_Dispatch | 3e0e3ec4645c4ff3af217919e9ff1571241949945ce97fd8cef4b73003c07b0f | 9a1735d4283e99df1bade285a1b412490332ea59fba180798949a9d1c8277c99 | 2ea2fce09ae0117bf36689d9ce99e923d618939ae4170eb426728d84a26d81bf | NNO_L008/receipt.json |
| NVR_DispatchEmitted | 3e0e3ec4645c4ff3af217919e9ff1571241949945ce97fd8cef4b73003c07b0f | 9be4f256f71a9d6939819e964dbf2627a210d56fc3c363cbc1394bcb402e1232 | 9bcb409ebed3c87e20520f5eb6d2207a15a1d9f002a05e093b912527f48fc18f | NNO_L009/receipt.json |
| NVR_Reify | 77594ff381c97eefa3950bf02720bce0b3c4c6033c6ee2ecc9f75c5efbf570d8 | e82e7ec012ed9d9ee046c7f2712c0cc2a6dfb3ea280c636a131001cb46b07f52 | 80a6e10760004c4dad31c418dbbc5e54681266012146482eb3cf8199bc261cb8 | NNO_L010/receipt.json |
| NVR_Folds | 52b1278f50887745697046d40366f97a00a72ec6ffee02f57e88ac8e48aa724f | c1f00adf3c272140fcecd49e8cb3627a5f2d58303be5d961fe52276fd6a334b5 | 75f1b6d6dad21f02e39e2660896809605f2c72797c380e89c5b223e7bc7d6f9d | NNO_L011/receipt.json |
| NVR_TAS | 481072b94cb0e3d248df8d8cd9a0b75d53ae365416c2eab941d7402c6cbfc7c4 | 576ec82935a5559b61d698385bfa416819a9ef5e5063523a92ffcbd3abd629fc | ce275d00a7f06b2721a65ad5e5d8eacdbaf48467426dd3984ff03f396791d2d8 | NNO_L012/receipt.json |
| NVR_NNCWeak | 2c4477bd06454d0ff695ff86a06d6592799f436e2ac84806663a9da326783c48 | 629b250899054a0dc088f5de73cbe35d36012963195c935e81c77d8ddc9fdd4c | 71c2ac9707db7e69c15096c7446d83ee86f1a5823d009b10e08056349638ba63 | NNO_L013/receipt.json |
| NVR_COMBINED_IMPORT | N/A: added combined coherence module | 19136eb460fde52e4085ef940d21214409f5f3cdf5b6451ade66814fe1fa8245 | a433ef31e21971f34b403f4f03b16d31ea197f400cafe23a8729510df97f71bf | NNO_L014/receipt.json |

Sources are the original `evidence/nvr-20261108/*.lean`; staged source hashes match. NNO_STATEMENT_COMPARISON.json compares every complete source declaration header with its NMV_/NNF_ original after the explicit namespace transport. All existing headers match; only the three specified rev4 NoWritePool helpers are added. This source comparison is distinct from the kernel statement export in NNO_StatementChecks; neither imports rev1 NMV_EXPORT/NNF_SEED objects. The inherited 15 unchanged NMV prerequisites are reused rather than duplicated. Extra inherited generic imports outside ledger29’s closure are disclosed in NNO_COHERENCE.json and subject to the final scan.

All NVR theorem print audits are standard-only in the module receipts; the three helper audits omitted by the original draft are included in NNO_StatementChecks. Frozen source, RowSpecs, hypotheses and trust are unchanged.

Final audit outcome: all five FIN raw ax2 walks and all eight fixtures PASS
(NNO_audit/final/proof0.json and fixtures.json). The combined NFX scan is
INCOMPLETE: its fallback driver failed to elaborate before scanning; neither
zero dangling references nor zero duplicate owners is established. The typed
modules-only correction is prepared but untested because24/24 scopes were
consumed. The exact checks emitted an object in L023; that scope's subsequent
native link failed. FIN RSS review is retrospective; no live1GiB stop receipt
was emitted. See NNO_HANDOFF.md and NNO_REMAINING.md for these limitations.

target not yet established
