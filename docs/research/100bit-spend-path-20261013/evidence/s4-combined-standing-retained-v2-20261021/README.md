# Retained combined-candidate native evidence

MEASURED: copied existing completed NUC evidence without rerunning any build or gate. The accepted run is standing-runner-v2/standing-result-v2.json, with 30 exit-zero command receipts against candidate artifact40dc7574. The earlier standing-runner attempt failed to locate cargo (exit127) and is not accepted evidence; it remains on the build host.

All30 accepted scopes record MemoryHigh2GiB/MemoryMax4GiB/MemorySwapMax0 and zero current swap. The six retained deterministic LiteSVM fixture reports give maximum stage1 1,210,100 CU and settlement1,189,265 CU, below the actual1,400,000 limit without a diagnostic override. Their candidate verifier hash matches the standing-run artifact. The default/devnet build comparison records identical.text and only the two deployment ID data slots differing.

These are finite native/fixture results, not soundness proofs, all-input CU bounds, proof of mask-value independence, candidate adoption or final release provenance. They do not satisfy the historical stage1-at-most-B1 performance criterion. Full recursive source/build inventories remain separate. Source hashes were re-read at collection and match the candidate overlay. The accepted run's original source revision/argv/resources are retained in its receipts. Output logs remain on the NUC with their exact hashes recorded here; only receipt/command/time records and public fixture evidence were copied. No keys, programs, proofs or compiled artifacts were copied or deleted.

Run python3 check_packet.py.
