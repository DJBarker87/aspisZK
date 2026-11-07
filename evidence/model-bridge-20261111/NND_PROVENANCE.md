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
