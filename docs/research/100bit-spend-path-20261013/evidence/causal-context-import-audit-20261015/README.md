# Present-cache provenance supplement

`present-cache-provenance.json` records direct imports of the eight causal-context targets with source and olean hashes observed in the pinned NUC workspace on 2026-10-15. These are present-cache observations, not claims about the exact files consumed by each earlier compile. Bundle-time source/object pins are included where available.

R572 has a historical source pin and successful compile receipt, plus a current overlay entry naming the NUC cache object's symlink target and hash. The historical receipt does not contain an output olean hash, and the overlay does not name that receipt; therefore those artifacts do not form a receipt-to-olean hash chain.
