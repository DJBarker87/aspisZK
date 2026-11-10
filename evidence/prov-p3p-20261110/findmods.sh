#!/bin/bash
# usage: bash findmods.sh Mod1 Mod2 ... ; prints the first LEAN_PATH dir holding each module olean (host, read-only)
P=../ledger30-20261111/NNN_PATHS.json
python3 - "$@" <<'PY' | ssh -o ConnectTimeout=20 -o ServerAliveInterval=15 dombarker@100.108.41.90 'timeout 80 python3 -c "
import sys,json,os
d=json.load(sys.stdin)
for m in d[\"mods\"]:
    r=[p for p in d[\"paths\"] if os.path.exists(p+\"/\"+m.replace(\".\",\"/\")+\".olean\")]
    print(m, r[:1])
"'
import sys,json
print(json.dumps(dict(mods=sys.argv[1:],paths=json.load(open('../ledger30-20261111/NNN_PATHS.json')))))
PY
