# Local evidence writer recovery

A local ENOSPC exception interrupted K087 collection. The preliminary prelaunch reading was corrected: read-only host recovery found an actual completed K087 receipt. It timed out (exit1,112.96045977598988 s,6402096 KiB RSS,swap0), so it was recovered without resubmission. The before-run frozen graph was already matched; after recovery Cargo.lock still matches the frozen hash. K088 is skipped, not launched.

The transport journal duplicated complete stdout/receipt/time payloads already retained in each attempt directory. NBZ_LOG_COMPACTION.json records its original/new SHA-256 and any partially written tail. It is now a hash/byte-count/tail index; full proof logs, full metadata graph outputs, receipts and source evidence are retained. The own logger now writes this compact index for new calls. No proof validation, cap or dependency rule changed. No shared or foreign files were removed.
