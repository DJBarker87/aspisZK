#!/bin/bash
# One focused NEW module only; the Python driver holds the shared BSD flock.
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
exec python3 "$HERE/compile.py" "$@"
