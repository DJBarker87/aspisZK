#!/bin/bash
# T2: toolchain/profile facts. Read-only.
W=/home/dombarker/project-offloads/codex-cx-l188-20261109; O=$W/analysis/profile; mkdir -p $O
PT=/home/dombarker/.cache/solana/v1.52/platform-tools
R=$PT/rust/bin/rustc
$R -vV > $O/rustc_vV.txt
$PT/rust/bin/cargo -vV > $O/cargo_vV.txt 2>&1
$PT/llvm/bin/clang --version > $O/clang_version.txt 2>&1
$PT/llvm/bin/ld.lld --version > $O/lld_version.txt 2>&1
cat $PT/version.md > $O/platform_tools_version.txt 2>/dev/null; ls $PT > $O/platform_tools_ls.txt
sha256sum $R $PT/rust/bin/cargo $PT/llvm/bin/ld.lld /home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf > $O/tool_sha256.txt
readlink -f /home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/platform-tools-sdk/sbf/dependencies/platform-tools >> $O/tool_sha256.txt
for t in sbpf-solana-solana; do RUSTC_BOOTSTRAP=1 $R -Z unstable-options --print target-spec-json --target $t > $O/target_spec_$t.json 2>&1; $R --print cfg --target $t > $O/cfg_$t.txt 2>&1; $R --print cfg --target $t -C opt-level=3 > $O/cfg_opt3_$t.txt 2>&1; done
for b in NOX_B002 NOX_B003; do grep -E 'Running `' $W/receipts/$b/stderr.log | grep -E -- '--crate-name (aspis_core|aspis_statement|aspis_r1_cost_probe|aspis_r1_cost_probe_program|solana_program) ' > $O/rustc_cmds_$b.txt; done
grep -E 'Running `|cargo-build-sbf|rustup|platform' $W/receipts/NOX_B002/stderr.log | grep -v -- '--crate-name' | head -40 > $O/driver_lines_B002.txt
