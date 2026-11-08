NNQ host O2 continuation. Branch codex/cx-dgo-host-20261107.

Items1-7 retain the original accepted NNQ_L001-L030 receipts and NNQ_COMBINED_IMPORT. The continuation closes:

| Item | Lean name in AspisR1.NNQ_HostDigest | Receipt |
|---|---|---|
|8|firstCode_eq, secondCode_eq; prepare_lower_eq, secondCommon_eq|NNQ_L031|
|9|child_sim; child_raw_sim for raw stage composition|NNQ_L032,034|
|10 account|caller_first_eq, caller_second_eq; firstSyntax_eq, secondSyntax_eq, account_withDigest|NNQ_L035,036|
|10 recorder/O2|observer_withDigest; o2 : AspisR1.DGP_HostDigest.O2|NNQ_L037,038|

O2 is proved with exactly the existing three hypotheses. Its statement is quoted verbatim in NNQ_O2.lean. No source/trust/model change, new premise or restriction of adversary/hashv/H. Standard axioms only: propext, Classical.choice, Quot.sound. No shipped files changed; inherited ELF pins are default f8c0ec72…, devnet63ad3e9c…, Pool e0e49c34… (owner amendment); no rebuild trigger.

NNQ_L033's memory-exhausted combined shape was split, then its replacement passed at L034/L035. No failed shape was rerun unchanged. Every launch used the unchanged 180s timeout, -j1 -M7000 async=false and a systemd scope (6G high,8G max,swap0,tasks64), fresh allowed:true/exit0 admission, whole-host scope count<6 and disk>=40GB. Exact target, source revision/hash, dependency fingerprint, exit, wall, peak RSS, swap and printed axioms are in NNQ_COMPILE.tsv and each receipt.json/stdout.log/time.log. NNQ_L038: exit0,4.271607455s,6703972KiB RSS,swap0; source revision fb3108aa636 with exact dirty source hash in receipt.

For NNH run6, prepend /home/dombarker/project-offloads/codex-cx-dgo-host-20261108/NNQ_objects to NNH_R4_objects:NNH_objects:NNH_seed:NNH_library_seed under /home/dombarker/project-offloads/codex-cx-integrate-20261111. Toolchain v4.32.0. NNH run5 workspace and objects were read-only. Final combined import and pins audit follow in the final stage.

Remaining integration: NNH_RecordedCharge.bound transported using O1/O2; same-world actual failure inclusion, condition(4), and the deployed headline. No NDT/headline credit. See NNQ_REMAINING.md. Stage commits local; no push.

target not yet established
