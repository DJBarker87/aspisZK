#!/usr/bin/env bash
# Refuse to relabel changed sources as this measured control.
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
check(){ [[ "$(sha256sum "$ex/$1" | cut -d' ' -f1)" == "$2" ]] || { echo "Wrong line-norm source: $1" >&2; exit 2; }; }
check relation_callback.rs 03cd2e627d825fc939e922916eace5670d816e238b6b575fb5f8e4184dc323e4
check circle_norm.rs 95985ca1a1d09f9e23805145f2dfd49c38016803844a768bd919bf4bbace7a1a
check joined_inverse.rs 5dc5bb8aa79c512867897e96eb09ab5a8879e65f73de2c2b10af872ccdcd5a32
check line_norm.rs 8f84072acbddf35b7e811036a093a0de4a31d44fc62223938cc0f87dcb153f05
