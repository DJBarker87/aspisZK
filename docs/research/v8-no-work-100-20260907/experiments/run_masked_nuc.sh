#!/usr/bin/env bash
# Run only inside the isolated NUC overlay, never write the shared cache.
set -euo pipefail
[[ $# == 3 ]] || exit 2
readonly task="$1" target="$2" tag="$3"
case "$task" in /home/dombarker/project-offloads/aspis-masked-tail.*) ;; *) exit 2 ;; esac
[[ "$target" =~ ^[A-Za-z][A-Za-z0-9]*$ && "$tag" =~ ^[a-z0-9-]+$ ]] || exit 2
readonly cache=/home/dombarker/project-offloads/ZK-v7-clean-k16-20260831/AspisFormal
readonly unit="aspis-tail-$tag"
readonly log="$task/$tag.log"
[[ ! -e "$log" && -e "$task/overlay/$target.lean" ]] || exit 2
cd "$cache"
readonly oldpath="$(/home/dombarker/.elan/bin/lake env printenv LEAN_PATH)"
readonly lean="$(/home/dombarker/.elan/bin/lake env which lean)"
python3 "$task/snapshot_masked_nuc.py" "$task" snapshot "$target" "$tag"
{
  printf 'REMOTE_TASK=%s\nTARGET=%s\nRESEARCH_PIN=b006d34ffc6d552cd5ecd9f292cf2bd095f7fdb9\nBORROWED_SOURCE_PIN=26a9cd4718aae9f9de7ef1c3394fb74a229085d5\n' "$task" "$target"
  "$lean" --version
  sha256sum "$task/$tag-manifest.json" "$task/overlay/$target.lean" "$task/run_masked_nuc.sh"
  python3 "$task/verify_masked_nuc.py" "$task" "$cache" "$tag-manifest.json"
  systemd-run --user --scope --quiet --unit="$unit" \
    -p MemoryHigh=5G -p MemoryMax=7G -p MemorySwapMax=0 -p CPUQuota=200% \
    env LEAN_PATH="$task/overlay:$oldpath" bash -c '
      set -uo pipefail
      task="$1"; target="$2"; lean="$3"
      cg="$(awk -F: '\''$1=="0" {print $3}'\'' /proc/self/cgroup)"
      printf "CGROUP=%s\n" "$cg"
      for setting in memory.high memory.max memory.swap.max cpu.max; do
        printf "%s=" "$setting"; head -n 1 "/sys/fs/cgroup$cg/$setting"
      done
      printf "COMMAND=%q -j1 -M6500 -R %q -o %q %q\n" "$lean" "$task/overlay" "$task/overlay/$target.olean" "$task/overlay/$target.lean"
      /usr/bin/time -v "$lean" -j1 -M6500 -R "$task/overlay" \
        -o "$task/overlay/$target.olean" "$task/overlay/$target.lean"
      result=$?
      printf "LEAN_EXIT=%s\n" "$result"
      if [[ "$result" == 0 ]]; then sha256sum "$task/overlay/$target.olean"; fi
      exit "$result"
    ' _ "$task" "$target" "$lean"
  python3 "$task/verify_masked_nuc.py" "$task" "$cache" "$tag-manifest.json"
  python3 "$task/snapshot_masked_nuc.py" "$task" record "$target" "$tag"
  echo PROVENANCE_UNCHANGED=true
} 2>&1 | tee "$log"
