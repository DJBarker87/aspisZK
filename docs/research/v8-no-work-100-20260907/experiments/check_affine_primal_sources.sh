#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
check(){ [[ "$(sha256sum "$ex/$1" | cut -d' ' -f1)" == "$2" ]] || { echo "Wrong affine-primal source: $1" >&2; exit 2; }; }
check relation_callback.rs 0518ede91b20718ee6b5d4030d8e8ef9e8cb2410a4532251e3e6e13316dfde4a
check affine_primal.rs 7a02acca95ef9256a0ea984136e7c2d315ca9e7b4f84559f85c5f22ca7e6a863
check quotient_fold.rs 65dcdc718b9e2e061d48fbe3de1ca6d69733f9156d1b78c9e2fed1e04a4df76d
check circle_norm.rs 95985ca1a1d09f9e23805145f2dfd49c38016803844a768bd919bf4bbace7a1a
check joined_inverse.rs 5dc5bb8aa79c512867897e96eb09ab5a8879e65f73de2c2b10af872ccdcd5a32
check line_norm.rs 8f84072acbddf35b7e811036a093a0de4a31d44fc62223938cc0f87dcb153f05
