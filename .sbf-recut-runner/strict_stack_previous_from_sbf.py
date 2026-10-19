#!/usr/bin/env python3
"""Strict lead gate: oversized diagnostics fail even if linker discards symbol."""
import argparse, hashlib, json, re, subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--log',required=True);p.add_argument('--linked',required=True);p.add_argument('--measured',required=True);p.add_argument('--output',required=True);a=p.parse_args()
log=Path(a.log);records=[];unknown=[]
for number,line in enumerate(log.read_text(errors='replace').splitlines(),1):
    if not re.search(r'Stack offset|[Ee]stimated (?:function )?frame size|stack frame size',line):continue
    offsets=[int(n) for n in re.findall(r'Stack offset(?: of)?\s+(-?\d+)',line)]
    frames=[int(n) for n in re.findall(r'[Ee]stimated (?:function )?frame size:?\s+(\d+)',line)]
    symbol=re.search(r'Function\s+(\S+)',line)
    record={'line':number,'diagnostic':line,'symbol':symbol.group(1) if symbol else None,'offsets':offsets,'frames':frames,'oversized':any(abs(n)>4096 for n in offsets+frames)}
    records.append(record)
    if not offsets and not frames:unknown.append(record)
result={'policy':'ANY oversized stack-offset/frame diagnostic fails, including dead/stripped functions','status':'FAIL' if any(r['oversized'] for r in records) or unknown else 'PASS','diagnostics':records,'unparsed':unknown,'inputs':{p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in [a.log,a.linked,a.measured]},'compiler_source_revision':'RECUT_REVISION_FROM_PHASE_RECEIPT'}
Path(a.output).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));raise SystemExit(0 if result['status']=='PASS' else 2)
