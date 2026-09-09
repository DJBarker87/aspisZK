#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
bash "$ex/check_shared_gamma_sources.sh"
[[ "$(sha256sum "$ex/query_arithmetic.rs" | cut -d' ' -f1)" == 0336ad35e37cae974d009d8db34e1abc75264a1437e1ccd76d76bd7df354bb68 ]] || exit 2
[[ "$(sha256sum "$ex/../../../../crates/aspis-core/src/field.rs" | cut -d' ' -f1)" == bb4b177e4b06da631cef8cc3eaa44b3b08c1bbf3b123b975b116264f447d8fe0 ]] || exit 2
