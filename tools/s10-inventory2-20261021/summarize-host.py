#!/usr/bin/env python3
"""Compact MIR/receipt evidence; raw bodies remain hash-pinned on the host."""
import collections,hashlib,json,re,subprocess,shutil
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-inventory2-20261021')
F=Path('/home/dombarker/project-offloads/codex-cx-s10-inventory-20261021')
O=H/'packet';O.mkdir(exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
def pin(p):return dict(path=str(p),sha256=sha(p.read_bytes()),bytes=p.stat().st_size)
def dump(p,x):
    raw=(json.dumps(x,indent=2,sort_keys=True)+'\n').encode()
    p.write_bytes(raw)
    assert len(raw)<=5_000_000,(p,len(raw))
def decode(s):
    s=re.sub(r'\\u\{([0-9a-f]+)\}',lambda m:chr(int(m[1],16)),s)
    return json.loads(s)
def normalize(s):
    parts=s.split('::')
    return '::'.join(parts[1:]) if len(parts)>1 and parts[0]==parts[1] else s
inputs=json.loads((F/'frozen-source-hashes.json').read_text())
files=inputs['files'];mismatches=[]
for f in files:
    p=F/'src'/f['path']
    if sha(p.read_bytes())!=f['sha256']:mismatches.append(f['path'])
assert not mismatches,mismatches
dump(O/'source-recheck.json',dict(frozen_source_revision=inputs['source_revision'],files=len(files),
    manifest=pin(F/'frozen-source-hashes.json'),mismatches=mismatches))
receipts=[];summaries=[];census=[]
for p in sorted(H.glob('*/receipt/receipt.json'))+sorted(H.glob('driver-compile-*/receipt.json'))+sorted(H.glob('elf-check-*/receipt.json')):
    r=json.loads(p.read_text());r['wrapper_source_revision']=r.pop('source_revision')
    r['frozen_source_revision']=inputs['source_revision'];r['receipt_pin']=pin(p)
    r['source_revision_note']='Wrapper checkout revision is not frozen input identity; see independently rehashed frozen copy.'
    out=O/'receipts'/p.parent.parent.name if p.parent.name=='receipt' else O/'receipts'/p.parent.name
    out.mkdir(parents=True,exist_ok=True)
    for q in p.parent.iterdir():
        if q.is_file() and q.name!='receipt.json':(out/q.name).write_bytes(q.read_bytes())
    command=p.parent.parent/'command.json';reservation=p.parent.parent/'reservation.json'
    if p.parent.name=='receipt':
        for q in [command,reservation]:
            if q.exists():(out/q.name).write_bytes(q.read_bytes())
    dump(out/'receipt.json',r);receipts.append(dict(name=out.name,receipt=r))
    tsv=p.parent.parent/'mir.tsv'
    if p.parent.name!='receipt' or not tsv.exists() or r['exit_status']!=0:continue
    # Keep final two-phase probes only; failed/earlier probes stay in receipts.
    name=p.parent.parent.name
    if not name.endswith(('-v7','-v9')):continue
    rows={};phase='optimized';calls=collections.Counter()
    for line in tsv.open():
        parts=line.rstrip('\n').split('\t');kind=parts[0]
        path=decode(parts[1]);row=rows.setdefault(path,dict(name=path,calls=[],indirect=[],drops=[],inlines=[],body_pins=[]))
        if kind=='D':row.update(span=decode(parts[2]),generics=parts[3])
        elif kind=='P':phase=decode(parts[2])
        elif kind=='C':
            row['calls'].append(dict(phase=phase,block=parts[2],target=normalize(decode(parts[3])),
                generics=decode(parts[4]),span=decode(parts[5]),arguments_sha256=sha(parts[6].encode())))
            calls[phase]+=1
        elif kind=='I':row['indirect'].append(dict(phase=phase,block=parts[2],operand=decode(parts[3]),span=decode(parts[4])))
        elif kind=='X':row['drops'].append(dict(phase=phase,block=parts[2],type=decode(parts[3]),span=decode(parts[4])))
        elif kind=='L':row['inlines'].append(dict(phase=phase,instance=decode(parts[2]),span=decode(parts[3])))
        elif kind=='B':row['body_pins'].append(dict(phase=phase,sha256=sha(decode(parts[2]).encode()),bytes=len(decode(parts[2]).encode())))
        elif kind=='K':row['constant_kind']=parts[2]
        elif kind=='E':row['elaborated_frontier']=decode(parts[2])
        else:raise AssertionError(kind)
    summary=dict(schema='s10-module-mir-summary-v1',name=name,raw=pin(tsv),generator='tools/s10-inventory2-20261021/summarize-host.py',
        command=json.loads(command.read_text()),counts=dict(declarations=len(rows),calls=dict(calls)),declarations=list(rows.values()))
    census.append(summary)
    summaries.append(dict(name=name,raw=pin(tsv),counts=summary['counts']))
census_path=H/'mir-census.json'
census_path.write_text(json.dumps(dict(probes=census),indent=2,sort_keys=True)+'\n')
if (O/'mir').exists():shutil.rmtree(O/'mir')
dump(O/'probe-manifest.json',dict(schema='s10-mir-probe-manifest-v1',source_revision=inputs['source_revision'],
    rustc_version=subprocess.check_output(['/home/dombarker/.cargo/bin/rustc','+nightly-2026-06-01','-Vv'],text=True),
    driver_source=pin(H/'mir_edges.rs'),driver=pin(H/'mir-edges'),probes=summaries,
    artifacts=[dict(**pin(census_path),generator='tools/s10-inventory2-20261021/summarize-host.py',retention='HOST ONLY: derived JSON exceeds 5 MB')],
    print_axioms='N/A: no new Lean theorem or formal release replay; first-pass four standard-axiom audits reused unchanged'))
(O/'elf-crosscheck.json').write_bytes((H/'elf-crosscheck.json').read_bytes())
print(json.dumps(dict(probes=len(summaries),census=pin(census_path),receipts=len(receipts))))
