#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
check(){ [[ "$(sha256sum "$ex/$1" | cut -d' ' -f1)" == "$2" ]] || { echo "Wrong terminal-query source: $1" >&2; exit 2; }; }
if [[ "${2:-build}" == test ]];then
 check relation_callback.rs 3c49fd8ccb5654dbe1067fbb5d923eec472fdff1e5303a558b778a53302d87a9
else
 check relation_callback.rs d7a6eff3f93e36a11525818f3fd672b1e60f71c1bf48138292cdc636ef3ba615
fi
check shared_gamma.rs 75c26014c9900221445c14536d966f3d9267b53b331709099afda6374bf72552
if [[ "${1:-terminal-prefix}" == terminal-stack ]];then
 check performance_verifier.rs cdccf89cba145831138e6ac93272e262e6e377f9ea9835058d0ceb38701d8c6e
else
 check performance_verifier.rs 4750bcfdec10cb562ca316704b1df8801d71e2b960f3f6a3961097a9b834e368
fi
check semantic_boundary.rs e4325326ab00bc26a855cb6ef1ee9996d7bb208585e2c2f63d643e08a2df89be
check semantic_carry.rs 2b8a5343bf81bd5695765b3a0a320120096e7c7699584b867b3a247b4d1bbc0f
check affine_primal.rs 7a02acca95ef9256a0ea984136e7c2d315ca9e7b4f84559f85c5f22ca7e6a863
check quotient_fold.rs 65dcdc718b9e2e061d48fbe3de1ca6d69733f9156d1b78c9e2fed1e04a4df76d
check circle_norm.rs 95985ca1a1d09f9e23805145f2dfd49c38016803844a768bd919bf4bbace7a1a
check joined_inverse.rs 5dc5bb8aa79c512867897e96eb09ab5a8879e65f73de2c2b10af872ccdcd5a32
check line_norm.rs 8f84072acbddf35b7e811036a093a0de4a31d44fc62223938cc0f87dcb153f05
case "${1:-terminal-prefix}" in
 terminal-prefix)
  check structured_weights.rs 8b3c9e45e15f74510b91ad10880b082eff08a62664eeb0eb18ef376433ce8835
  check terminal_query.rs d68591b720f2a1e3d627376cb2e2aefa5dd4c623e1b89b4f6f4175b1743401bb
  check ../../../../crates/aspis-core/src/sumcheck.rs 7e12acf033a9c309a836dcb1c334c69932e15b97407613b3968f8e1c53787ead;;
 terminal-fixed)
  check structured_weights.rs 8b3c9e45e15f74510b91ad10880b082eff08a62664eeb0eb18ef376433ce8835
  check terminal_query.rs af1f38cefe7e271dae61e0dc44fcdd88defe14984c6fc26d2b11642d0530a65c
  check ../../../../crates/aspis-core/src/sumcheck.rs c89f1df5cc4928e852bedeb886f9179998b1cbb12c603b280e26dddaef61e72a;;
 terminal-fused|terminal-stack)
  check structured_weights.rs 06befd20c084234ce1afa2d7cf3612a12370fdb0e98e95db30d89cf245b51089
  check terminal_query.rs f51699776c77d2fc9e0fc9dfdd08ed9530b82230a068bdcedf919aefe240ee82
  check ../../../../crates/aspis-core/src/sumcheck.rs c89f1df5cc4928e852bedeb886f9179998b1cbb12c603b280e26dddaef61e72a;;
 *) exit 2;;
esac
check query_arithmetic.rs 57590907abf1c6a278cca0babc49b4c916a87a0a44e1f265b9bea28cc9fd52b1
check ../../../../crates/aspis-core/src/field.rs bb4b177e4b06da631cef8cc3eaa44b3b08c1bbf3b123b975b116264f447d8fe0
