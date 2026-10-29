#!/bin/sh
set -eu
H=/home/dombarker/project-offloads/codex-pv-c474-20261029
python3 "$H/corpus.py"
python3 "$H/corpus-audit.py"
