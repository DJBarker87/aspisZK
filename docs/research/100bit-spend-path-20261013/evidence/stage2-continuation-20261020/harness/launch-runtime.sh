#!/bin/sh
# From the worktree: launch-runtime.sh <new namespace> <previous source revision> <previous namespace>
set -eu
E=docs/research/100bit-spend-path-20261013/evidence/stage2-continuation-20261020
H=/home/dombarker/project-offloads/codex-cx-stage2b-20261020
REMOTE=dombarker@100.108.41.90
TAG=$1
python3 "$E/harness/prepare-runtime.py" "$TAG"
ssh "$REMOTE" "mkdir -p $H/artifacts/source-$2-cu-failed $H/harness-$TAG; cp $H/artifacts/verifier/* $H/artifacts/source-$2-cu-failed/; cp $H/cu-$3.json $H/cu-source-$2-failed.json"
scp -r "$E/harness/$TAG/." "$REMOTE:$H/harness-$TAG/"
scp "$E/pins/build-inputs.json" "$REMOTE:$H/pins/build-inputs.json"
ssh "$REMOTE" "python3 - <<'PY'
from pathlib import Path
import json,hashlib
H=Path('$H');j=json.loads((H/'pins/build-inputs.json').read_text())
for f in j['files']:assert hashlib.sha256((H/'src'/f['path']).read_bytes()).hexdigest()==f['sha256'],f['path']
(H/'source-revision.txt').write_text(j['base_revision']+'\n')
print('verified',len(j['files']),j['base_revision'])
PY
chmod +x $H/harness-$TAG/capped-run.sh $H/harness-$TAG/sbf-linker/rust-lld
sh $H/harness-$TAG/all.sh"
