#!/bin/sh
# L187 final (b), one step per invocation; argv: step. Each step runs inside its own capped scope (launched by the caller).
set -u
W=/home/dombarker/project-offloads/codex-cx-replay-l187-20261109; T=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0
F=$W/final; mkdir -p $F/objs $F/tmp
export PATH=/usr/bin:/bin LEAN_SYSROOT=$T TMPDIR=$F/tmp LEAN_PATH=$F/objs:$W/objs:$W/base_ref
cd $F
case "$1" in
 statements) /usr/bin/time -v -o statements.time timeout 600 $T/bin/lean -j1 -M7000 -DElab.async=false -R $F/src -o $F/objs/NNH8_Statements.olean $F/src/NNH8_Statements.lean > statements.log 2>&1; echo exit=$? >> statements.log;;
 combined) /usr/bin/time -v -o combined.time timeout 600 $T/bin/lean -j1 -M7000 -DElab.async=false -R $F/src -o $F/objs/TAS_G0_COMBINED_IMPORT.olean $F/src/TAS_G0_COMBINED_IMPORT.lean > combined.log 2>&1; echo exit=$? >> combined.log;;
 combined16) /usr/bin/time -v -o combined16.time timeout 600 $T/bin/lean -j1 -M15000 -DElab.async=false -R $F/src -o $F/objs/TAS_G0_COMBINED_IMPORT.olean $F/src/TAS_G0_COMBINED_IMPORT.lean > combined16.log 2>&1; echo exit=$? >> combined16.log;;
 ax2) # $2 attempt dir name, $3 comma roots
   python3 - "$2" "$3" <<'PY'
from pathlib import Path
import json,hashlib,subprocess,sys,os
walker=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNM_20261111/NNM_native/NNM_ProofDriver')
assert hashlib.sha256(walker.read_bytes()).hexdigest()=='46ee271b392729449147b978830b474e3fa4ecba2b45e03ad13c02490ba6ca3c'
a,roots=sys.argv[1],sys.argv[2].split(',')
out=Path.cwd()/a/'audit';out.mkdir(parents=True,exist_ok=True);os.chdir(out)
Path('NLX_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots])))
Path('NLX_AUDIT_MODULES.json').write_text(json.dumps([['TAS_FinalB']]))
with open('../stdout.log','w') as f: r=subprocess.run(['/usr/bin/time','-v','-o','../time.log',str(walker),'proof0'],stdout=f,stderr=subprocess.STDOUT)
sys.exit(r.returncode)
PY
   echo exit=$?;;
 nfx) /usr/bin/time -v -o nfx.time timeout 600 /home/dombarker/project-offloads/codex-cx-integrate-20261111/NNH_native/NNH8_RuntimeScan scan $F/L187_LOADED_scan.jsonl > nfx.log 2>&1; echo exit=$? >> nfx.log;;
esac
