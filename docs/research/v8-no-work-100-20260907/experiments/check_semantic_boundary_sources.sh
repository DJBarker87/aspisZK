#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
check(){ [[ "$(sha256sum "$ex/$1" | cut -d' ' -f1)" == "$2" ]] || { echo "Wrong semantic-boundary source: $1" >&2; exit 2; }; }
check relation_callback.rs 3a22d1c44a1c3bacdbbb0272d5ab540bda8d0f5cb06025e3f752684053fa75cb
check performance_verifier.rs 4750bcfdec10cb562ca316704b1df8801d71e2b960f3f6a3961097a9b834e368
check semantic_boundary.rs e4325326ab00bc26a855cb6ef1ee9996d7bb208585e2c2f63d643e08a2df89be
check semantic_carry.rs 2b8a5343bf81bd5695765b3a0a320120096e7c7699584b867b3a247b4d1bbc0f
check affine_primal.rs 7a02acca95ef9256a0ea984136e7c2d315ca9e7b4f84559f85c5f22ca7e6a863
check quotient_fold.rs 65dcdc718b9e2e061d48fbe3de1ca6d69733f9156d1b78c9e2fed1e04a4df76d
check circle_norm.rs 95985ca1a1d09f9e23805145f2dfd49c38016803844a768bd919bf4bbace7a1a
check joined_inverse.rs 5dc5bb8aa79c512867897e96eb09ab5a8879e65f73de2c2b10af872ccdcd5a32
check line_norm.rs 8f84072acbddf35b7e811036a093a0de4a31d44fc62223938cc0f87dcb153f05
