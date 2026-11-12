#!/bin/bash
# Aspis translatability pass, patch 0 (restoration of the pinned text of R1 functions under #[cfg]).
# Gate set by the lead for this patch: the deployed build must not change at all.
#   1 program built from <tree> with the deployed feature set; cmp with the base ELF
#   2 program built from <tree> with R1's feature set (pool-adapter,private-leaf-salts); cmp with devnet/verifier-pin2.so
# Usage: fv_tp1_p0.sh <name> <tree> <base-elf>     Time is expected in the two SBF builds (cold target directory).
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
N=$1; S=$2; BASE=$3
K=pool-adapter,future-one-tx-lean,private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place,future-lazy-horner,future-fold-shared
D=$W/TP1_$N.done; : > $D
bash fv_slot.sh TP-B-$N 3000 bash $W/fv_build_adapter_src.sh $N $K $S; echo "deployed build exit $?" >> $D
E=$W/out/$N/artifacts/aspis_r1_cost_probe_program.so
sha256sum $E $BASE >> $D 2>&1
if cmp -s $E $BASE; then echo "DEPLOYED ELF IDENTICAL TO BASE" >> $D; else echo "DEPLOYED ELF DIFFERS FROM BASE ($(stat -c %s $E 2>/dev/null) vs $(stat -c %s $BASE 2>/dev/null) bytes)" >> $D; fi
bash fv_slot.sh TP-B-$N-r1 3000 bash $W/fv_build_adapter_src.sh $N-r1 pool-adapter,private-leaf-salts $S; echo "R1-feature build exit $?" >> $D
R=$W/out/$N-r1/artifacts/aspis_r1_cost_probe_program.so
sha256sum $R $W/devnet/verifier-pin2.so >> $D 2>&1
if cmp -s $R $W/devnet/verifier-pin2.so; then echo "R1-FEATURE ELF IDENTICAL TO devnet/verifier-pin2.so" >> $D; else echo "R1-FEATURE ELF DIFFERS FROM devnet/verifier-pin2.so ($(stat -c %s $R 2>/dev/null) vs $(stat -c %s $W/devnet/verifier-pin2.so 2>/dev/null) bytes)" >> $D; fi
echo DONE >> $D
