#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
check(){ [[ "$(sha256sum "$ex/$1" | cut -d' ' -f1)" == "$2" ]] || { echo "Wrong query-injection source: $1" >&2; exit 2; }; }
check relation_callback.rs ff29f8d7a074dc04b5877505eafb4b55b38d2218a20357d1e744434eabe7b6f9
check structured_weights.rs 81f1ca25b4be65f10247e24320e6fb3ecc4b1e69e6ae06476c3ecf4cf501f631
check shared_gamma.rs 75c26014c9900221445c14536d966f3d9267b53b331709099afda6374bf72552
check performance_verifier.rs 4750bcfdec10cb562ca316704b1df8801d71e2b960f3f6a3961097a9b834e368
check semantic_boundary.rs e4325326ab00bc26a855cb6ef1ee9996d7bb208585e2c2f63d643e08a2df89be
check semantic_carry.rs 2b8a5343bf81bd5695765b3a0a320120096e7c7699584b867b3a247b4d1bbc0f
check affine_primal.rs 7a02acca95ef9256a0ea984136e7c2d315ca9e7b4f84559f85c5f22ca7e6a863
check quotient_fold.rs 65dcdc718b9e2e061d48fbe3de1ca6d69733f9156d1b78c9e2fed1e04a4df76d
check circle_norm.rs 95985ca1a1d09f9e23805145f2dfd49c38016803844a768bd919bf4bbace7a1a
check joined_inverse.rs 5dc5bb8aa79c512867897e96eb09ab5a8879e65f73de2c2b10af872ccdcd5a32
check line_norm.rs 8f84072acbddf35b7e811036a093a0de4a31d44fc62223938cc0f87dcb153f05
check query_arithmetic.rs 57590907abf1c6a278cca0babc49b4c916a87a0a44e1f265b9bea28cc9fd52b1
case "${1:-query-injection}" in
 query-injection-retained-powers) check query_injection.rs 2859fc037dc4075ba55c9316b6bfb2b1553177d7320728ed17af95a6db2bc30c;;
 query-injection) check query_injection.rs d4f7979118374f9e12d62e2ccba3b9e2f636bb0c02e93d2b32a5c538ee328781;;
 query-injection-fixed) check query_injection.rs 44bb2d4a49a5046a8f50ec32d9d6f3b460532fe3e1b81fcfaa47d900bf5a7efc;;
 *) exit 2;;
esac
check ../../../../crates/aspis-core/src/field.rs bb4b177e4b06da631cef8cc3eaa44b3b08c1bbf3b123b975b116264f447d8fe0
