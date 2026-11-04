# Stage 1: isolated source and validator preflight

Own source/cache setup passed host admission. NEW_CACHE_IMPORTS.json records 4,865 imported source/object records, including the 29 NET exports; predecessors remain read-only. SInt2 objects and Aeneas objects stay pinned by the compile driver.

Unchanged NET validator replay passed; the additive NEW validator retains 61/78 functions, 122 slice occurrences and 164/257 edges, both roots OPEN. Eight NEW validator tests passed (63.817s); eleven geometry source mutations/invariants passed. First read-only validator runs failed on missing sparse dependencies; git sparse-checkout add restored only the required committed paths. No inherited validator source changed.

NEW_K001 had an own cfg-prefix adaptation error and was cancelled while the lead shim waited outside any scope. It has no runner receipt, no credit and is not counted as an executed Kani run. NEW_K001_EXCLUDED.json retains the cancellation and transport record. NEW_K002 uses the corrected NET_reserve_only flag; source-flag existence is checked before admission. An intermediate driver syntax error was repaired before any K002 admission/launch.

NEW_K002 is submitted once and waiting in the lead quiet-window shim (until 2026-11-04 01:37:50 UTC). No source inputs will change while it is pending. Do not resubmit. Next: matched reserve control, TX2 reverse and controls, then the independent NEW_GeometryReverse proof.

No new composed row, ELF reproduction, source-to-ELF proof, or security conclusion. No shipped source/key change; no push.
