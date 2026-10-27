# Forest gates

The complete forest source snapshot is commit 7b8422542c. Host check03 passed with optimized-terminal,r1p-check,ct-host-prover. Pin gates after this source change:

|Mode|Receipt|SHA256|Result|
|---|---|---|---|
|default|forest-complete-elf-01-default|f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4|match|
|devnet|forest-complete-elf-01-devnet|63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299|match|
|Pool|forest-complete-elf-02-pool|121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548|match|

Pool01 was refused before launch at 15:11:46 UTC (allowed:false, exit78, 51,405,389,824 reserved + 8,589,934,592 requested > 59,055,800,320 safe bytes). Pool02 was invoked after the three-minute interval and passed. No unchanged successful ELF replay was repeated: default/devnet were omitted on the Pool-only retry. The initial partial snapshot's three pins are retained separately.

No Lean/Kani attempts have been made. No source-law, copy equality, native-effect transport, privacy premise removal, fixture gate or cost gate is claimed by these artifact matches. Target not yet established.
