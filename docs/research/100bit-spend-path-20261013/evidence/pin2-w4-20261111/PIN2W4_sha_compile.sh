#!/bin/zsh
# Compile the PIN2 SHA-256 seed layer in import order (blocks 00..25, then SeedHash).
EV=${0:A:h}
for i in $(seq -w 0 25); do
  M=NDO_JFp_SHABlock$i
  if [ $i = 25 ]; then N="W4 NEW module: 26th SHA block of the 1,595-byte PIN2 frame (generator JFp_generate_sha.py, PIN2 inputs)"; else N="W4 PIN2 REGEN (JFp_generate_sha.py, PIN2 frame)"; fi
  SRCDIR=$EV/sources $EV/PIN2W4_compile.sh $M "$N" || exit 1
done
SRCDIR=$EV/sources $EV/PIN2W4_compile.sh NDO_JFp_SeedHash "W4 PIN2 REGEN (parametric JFp_generate_seed, 26 blocks; statement change rawLength 1530->1595)"
