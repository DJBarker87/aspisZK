#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
bash "$ex/check_shared_gamma_sources.sh"
check(){ [[ "$(sha256sum "$ex/$1" | cut -d' ' -f1)" == "$2" ]] || { echo "Wrong query-affine source: $1" >&2; exit 2; }; }
case "${1:-query-affine}" in
 query-affine) check query_arithmetic.rs 7fe8118f97a90682d697aa967860418bc697acb3e5291fec51e93eb638f36e0a
  check query_affine_field.rs 23a2289d3562303a4cf52a72deb4e75ca5aecaab62cf00066d8f07017d467725;;
 query-affine-seeded) check query_arithmetic.rs 7fe8118f97a90682d697aa967860418bc697acb3e5291fec51e93eb638f36e0a
  check query_affine_field.rs 0fadc5f3e43e2e48861dffce045addd7721fbbcf982ecef9ad80a0a665122fbe;;
 query-affine-canonical) check query_arithmetic.rs 1ad3e13d8d84616139c6d15e5868e18279a9a552ba474618247f1303b562f54f;;
 *) exit 2;;
esac
check ../../../../crates/aspis-core/src/field.rs 4d9a92f586b63485e1381653a1bc67d54dc20622a467aee4d0da20a571aeefca
