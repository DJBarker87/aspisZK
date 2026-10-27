D298 starts from 9ff5a4594e, with no implementation/proof source edits.
The prepared branch initially occupied pv-cb3; git worktree move placed it at
requested pv-cb without changing branch or HEAD. Existing host/evidence run
from 0c9dc9a4cc is preserved; D298 uses its own subdirectory.
Default/devnet succeeded directly. Pool: one aggregate reservation refusal,
three-minute cooldown, next fresh label admitted; compiler helper-thread
WouldBlock failure (1.029s,173256KiB,swap0) before project compilation. A changed
retry adds taskset --cpu-list 0-3 with unchanged -j4 and 6G/8G/swap0/Tasks64 caps.
Native compilation also receives this affinity proactively; runtime fixtures do not.
No failed build was rerun unchanged; no memory cap was raised.
Initial source upload preceded recording a separate upload reservation receipt;
build reservation and barrier both passed before any compilation. This ordering
missed local-lean rule7's pre-scp receipt requirement. Subsequent baseline and
runner uploads have dedicated admission receipts. No shared env-J source/object
was written. Scope execution is serial. SBF diagnostics include the same stack
warnings as predecessor builds; the byte-equal requested pins are the gate.
