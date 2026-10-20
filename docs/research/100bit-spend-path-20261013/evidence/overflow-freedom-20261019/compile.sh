#!/bin/bash
# One focused module; Python holds the shared mkdir lock.
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
exec python3 "$HERE/compile.py" "$@"
