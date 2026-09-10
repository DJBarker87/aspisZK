#!/usr/bin/env bash
# One optimized exact small-field regression, never a package or Lean build.
set -euo pipefail
[[ $# == 2 ]] || exit 2
readonly task="$1" tag="$2"
case "$task" in /home/dombarker/project-offloads/aspis-identity-support.*) ;; *) exit 2 ;; esac
[[ "$tag" =~ ^[a-z0-9-]+$ ]] || exit 2
readonly source="$task/IdentitySupportCubicControl.rs"
readonly executable="$task/identity-support-$tag"
readonly log="$task/$tag.log"
readonly snapshot="$task/$tag-source.txt"
readonly runner_snapshot="$task/$tag-runner.txt"
readonly sourcehash=fcefe508cedebd8b481ac8a2c4ac75426d0fe3acfcf15ff390d11c042cc7ac4d
[[ -f "$source" && ! -e "$executable" && ! -e "$log" && ! -e "$snapshot" && ! -e "$runner_snapshot" ]] || exit 2
[[ "$(sha256sum "$source" | awk '{print $1}')" == "$sourcehash" ]] || exit 2
cp -p "$source" "$snapshot"
cp -p "$task/run_identity_support_control.sh" "$runner_snapshot"
{
  printf 'SOURCE_PARENT=e969d9fa5378dd1e548c8b64b79a9e76a2270d66\n'
  printf 'EXPECTED_WORK=optimized_compile_then_6145149_tiny_degree2_codewords_and_exact_polynomial_checks\n'
  sha256sum "$source" "$snapshot" "$task/run_identity_support_control.sh" "$runner_snapshot"
  systemd-run --user --scope --quiet --unit="aspis-identity-support-$tag" \
    -p MemoryHigh=1G -p MemoryMax=2G -p MemorySwapMax=0 -p CPUQuota=200% \
    bash -c '
      set -uo pipefail
      source="$1"; executable="$2"
      ulimit -t 60
      cg="$(awk -F: '\''$1=="0" {print $3}'\'' /proc/self/cgroup)"
      printf "CGROUP=%s\n" "$cg"
      for setting in memory.high memory.max memory.swap.max cpu.max; do
        printf "%s=" "$setting"; head -n 1 "/sys/fs/cgroup$cg/$setting"
      done
      /home/dombarker/.cargo/bin/rustc --version
      printf "COMPILE_COMMAND=/home/dombarker/.cargo/bin/rustc --edition=2021 -O -C overflow-checks=yes %q -o %q\n" "$source" "$executable"
      /usr/bin/time -v /home/dombarker/.cargo/bin/rustc --edition=2021 -O -C overflow-checks=yes "$source" -o "$executable"
      result=$?
      printf "COMPILE_EXIT=%s\n" "$result"
      [[ "$result" == 0 ]] || exit "$result"
      sha256sum "$executable"
      printf "CONTROL_COMMAND=%q\n" "$executable"
      /usr/bin/time -v "$executable"
      result=$?
      printf "CONTROL_EXIT=%s\n" "$result"
      exit "$result"
    ' _ "$source" "$executable"
  [[ "$(sha256sum "$source" | awk '{print $1}')" == "$sourcehash" ]]
  echo SOURCE_UNCHANGED=true
} 2>&1 | tee "$log"
