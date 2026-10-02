# R374 evidence bundle

This bundle preserves the successful and failed focused Lean runs, exact source snapshots, receipts, runner, direct import and proof-route source copies, pinned polynomial API/cache inventory, and read-only selector-coordinate census. `inventory.json` records the exact target and run measurements. The selector inventory is source-coordinate evidence only and does not state a polynomial degree result.

Run `python3 verify_evidence.py` from this directory to check the saved evidence offline. It does not invoke Lean, access the network, rebuild a cache, or depend on `.r21-scratch` paths. `collect_inventory.py` is retained inside `api-cache-inventory` as provenance; the offline evidence verifier does not run it.

The outer `SHA256SUMS` lists all bundle files except itself. The nested API/cache inventory keeps its own independent checksum file. Historical failed drafts are retained as failed runs; their `sorryAx` reports are not successful proof evidence.
