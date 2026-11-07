# Historical emission provenance

AdapterRw was emitted from 81521c77f7 plus the retained candidate overlay, not from the bare parent revision. lib.rs and r1_pool_adapter.rs hashes in candidate-sources.json equal frozen4bb3b3f. Owned source differs exactly in require_zero (index loop to suffix loop), with all other branches byte-identical. The complete differing hunk is retained below. TX2 definitions therefore need nominal/callee transport, with no source branch change; TX1 also needs the zero-loop equivalence. This does not imply source-to-ELF release reproduction.

```diff
--- candidate-owned
+++ frozen-owned
@@ -70,11 +70,10 @@
     }
     Ok(())
 }
-fn require_zero(bytes: &[u8]) -> ProgramResult {
-    let mut index = 0;
-    while index < bytes.len() {
-        if bytes[index] != 0 { return Err(ProgramError::AccountAlreadyInitialized); }
-        index += 1;
+fn require_zero(mut remaining: &[u8]) -> ProgramResult {
+    while !remaining.is_empty() {
+        if remaining[0] != 0 { return Err(ProgramError::AccountAlreadyInitialized); }
+        remaining = &remaining[1..];
     }
     Ok(())
 }
```

The complete local234 returned bridge now uses the fresh E001 replay and its per-definition equality. Fresh NMT E001/E002/E003 replays supply the 094/328/345 parent equalities; reused NMS/NMX receipts supply the241/242/233 links. These links do not silently discharge opaque children. The exact failed E002 zero extraction is retained; historical index-loop and CLOSED bounded native reference transports are support, not a fresh frozen emission. NMW dispatch remains context only and no NND wrapper equality is claimed.

Final tree-level source check (NND_FROZEN_SOURCE_CHECK.json): crates, programs/r1-cost-probe and Cargo.lock equal 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; programs/aspis-pool equals b936275465. No shipped change was made, so the conditional three-ELF rebuild is not triggered. Historical ELF pins are not a new reproduction result.
