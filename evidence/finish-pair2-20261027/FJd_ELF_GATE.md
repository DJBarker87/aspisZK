# Required rebuild gate

Default: build exit0,83.160577903s,649372KiB,swap0. Artifact1563728 bytes.
Expected f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4.
Actual ff08959936193ef00334ddd39e28b9546a331257749972494e3c30c338603bd5.
**Pin mismatch: gate FAILED.** No replacement pin is adopted.

The harness is standalone; the rebuilt corpus was unchanged and read-only.
This is a new private output/cache path using the historical feature/argv
recipe and optimized build scripts, not a claim of the unresolved historical
SBF exact-environment recapture. Compiler stack-offset diagnostics are in the
retained stdout; exit0 does not certify runtime safety.

Devnet: exit0,2.756459572s,203776KiB,swap0,1563728 bytes.
Expected63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299.
Actual8f6951609a7189ad3b43fd96ad2894a28e557cbeaf66a7823461e07208408cfd.
Pool: exit0,31.920898798s,643824KiB,swap0,605704 bytes.
Expected121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
Actual6a237e14843d8ae8bd65b4acbaf1754dd85ce1ed865479e9f50278f15d6305eb.

All three are failed pin comparisons. The initial diagnostic command omitted
the historical compiler wrapper; it cannot be called an exact replay. The
historical `/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023/src`
and its wrapper no longer exist (read-only inspection returned No such file
or directory). The recapture corpus and its retained wrapper exist. No
workspace or launcher was rebuilt to recreate the missing historical paths.
