# NIU own-input repairs

L002: owner-inspection input manifest was not uploaded by NIU runner. No theorem error, timeout or memory kill. Added the unchanged NIU_AUDIT_ROOTS.json input for the inspector before L003; validation unchanged.

The serial-client guard refused a premature queue invocation while L003 was running; no second scope was launched. After L003 completed the queue proceeded normally. The transient guard was inadvertently staged in the stage1 commit and is removed from the final tree when the client exits.

Read-only NIH validation initially lacked sparse NHU/NHG dependencies; git sparse-checkout add restored the committed directories without modifying them. Both inherited validators then passed. NIS report output was relocated solely to NIU_NIS_REVALIDATION.json; no sibling file was written.

Added the final close-only pin/export mode to the owned runner/batch scripts. Raw execution still uses the unchanged optimized proof binary and identical root groups, fixtures and walker. All script versions are source-snapshotted per scope.

Transcript hygiene deviation: initial source-inspection output and an overly broad file inventory were verbose. Subsequent launch/audit results use one-line summaries. This changed no source, gate, scope admission or credit.
