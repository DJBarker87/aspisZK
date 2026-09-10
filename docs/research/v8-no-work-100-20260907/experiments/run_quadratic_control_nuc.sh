#!/usr/bin/env bash
set -euo pipefail
task=${1:?task directory}
tag=${2:?fresh attempt tag}
[[ "$task" == /home/dombarker/project-offloads/aspis-higher-y.* ]]
[[ "$tag" =~ ^quadratic-control-nuc-v[0-9]+$ ]]
[[ ! -e "$task/$tag.log" ]]
src="$task/quadratic_specialization_control.rs"
cp "$src" "$task/$tag-source.txt"
{
  date -u '+UTC=%Y-%m-%dT%H:%M:%SZ'
  printf 'PARENT=%s\n' 289d7356c78a4cd493fe61a54f9548f2a0c11298
  printf 'SOURCE_SHA256='
  sha256sum "$src"
  /home/dombarker/.cargo/bin/rustc --version
  printf '%s\n' 'SCOPE=MemoryHigh=1G MemoryMax=2G MemorySwapMax=0 CPUQuota=200%' \
    'EXPECTED_WORK=optimized standalone compilation, then fixed 15625-family polynomial-determinant control'
  systemd-run --user --scope --quiet --unit="$tag" \
    -p MemoryHigh=1G -p MemoryMax=2G -p MemorySwapMax=0 -p CPUQuota=200% \
    bash -c '
      set -euo pipefail
      task=$1
      tag=$2
      systemctl --user show "$tag.scope" -p MemoryHigh -p MemoryMax -p MemorySwapMax -p CPUQuotaPerSecUSec
      printf "%s\n" "COMPILE=rustc --edition=2021 -O quadratic_specialization_control.rs"
      /usr/bin/time -v /home/dombarker/.cargo/bin/rustc --edition=2021 -O "$task/quadratic_specialization_control.rs" -o "$task/$tag.bin"
      printf "%s\n" "EXECUTE=$task/$tag.bin"
      /usr/bin/time -v "$task/$tag.bin"
    ' _ "$task" "$tag"
} 2>&1 | tee "$task/$tag.log"
