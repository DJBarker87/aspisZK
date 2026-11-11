#!/bin/bash
W=/home/dombarker/project-offloads/codex-pc-pin2-elf-20261111
cd $W
bash PCXS_elf_scope.sh PCXS_B001 build bash $W/PCXS_elf_build.sh PCXS_B001 default r1
bash PCXS_elf_scope.sh PCXS_B002 build bash $W/PCXS_elf_build.sh PCXS_B002 retarget r1
bash PCXS_elf_scope.sh PCXS_B003 build bash $W/PCXS_elf_build.sh PCXS_B003 default upload
echo done > $W/DRIVER_DONE
