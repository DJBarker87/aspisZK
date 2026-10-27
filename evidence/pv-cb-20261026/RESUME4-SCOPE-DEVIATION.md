# Scope scheduling deviation

During resume after context compaction, Kani gate7 and Lean queue38391–38393 were accidentally started concurrently. This violates the common instruction of at most one capped scope for this job. The Lean queue finished (two passes, one rejected proof); no result from it closes a source row. The Kani gate retained the unchanged 6G/8G/swap0/Tasks64 cap. Subsequent host scopes are strictly sequential. No cap or shared infrastructure was changed. Receipts preserve the actual runs.
