# Chain A families

The complete selected-certificate inventory is independently re-enumerated by NGE_certificates.py before compilation: 19,176 recursive records, 257 distinct names across 89 selected certificates. NFY_AUXILIARY_INPUTS pins original sources and bottom-up order. NGE_PROVENANCE stores every before/after body and import mapping; generator --check verifies deterministic reproduction.

| Family | New modules | Named public top theorems | Direct historical affected rows (overlap) |
|---|---:|---:|---:|
| NEE | 1 | 3 | 2 |
| NEJ | 5 | 10 | 6 |
| NEL | 7 | 19 | 8 |
| NEM | 7 | 21 | 21 |
| NEQ | 8 | 26 | 10 |
| NBN | 2 | 2 | 0 |

Eight S2K dependencies reuse the exact canonical JHb counterparts in NFY. NGE_SHARED_REUSE_DIFFS.json and NGE_PROVENANCE shared_owner_reuse assert their non-import bodies are byte-identical. No shared owner is redefined. The only changed proof-helper qualification is the emitted decoder map_err in NBN_ResultValidator, justified by NFY_OwnerTransport.map_err_transport.

No unreused NED/NEX/NEY edge occurs in this dependency closure. Existing NFY counterparts are read-only canonical inputs; absent NEX/NEY auxiliaries remain chain B. No historical native certificate or runtime trust row is replaced. Final closure is governed by NGE_LEDGER_DELTA.json after combined raw/fixture/scan and complete certificate-name checks; compilation alone gives no row credit.
