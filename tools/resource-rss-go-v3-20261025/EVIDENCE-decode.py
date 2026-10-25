"""Offline decode and byte audit only; no host operations."""
import json,hashlib,base64
from pathlib import Path
OUT=Path(__file__).resolve().parents[2]/'evidence/resource-rss-go-v3-20261025'
def pin(b):return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
paths=sorted(OUT.glob('EVIDENCE-transport-*-stdout.bin'))
transport={};inventory={};pending=b'';group=bytearray();groupid=0;current=None
frames=[]
def flush():
    global group,groupid
    if not group:return
    path=OUT/f'EVIDENCE-frames-{groupid:03}.jsonl'
    with path.open('xb') as f:f.write(group)
    frames.append(dict(path=path.name,**pin(group)))
    groupid+=1;group=bytearray()
for path in paths:
    b=path.read_bytes();transport[path.name]=pin(b);pending+=b
    while b'\n' in pending:
        line,pending=pending.split(b'\n',1)
        if len(group)+len(line)+1>4_500_000:flush()
        group.extend(line+b'\n');obj=json.loads(line)
        kind=obj['kind']
        if kind=='begin':
            assert current is None
            current=obj['name'];h=hashlib.sha256();size=0;seq=0
            inventory[current]=dict(status='PRESENT',pre_stat=obj['stat'],size=obj['size'])
        elif kind=='chunk':
            assert obj['name']==current and obj['seq']==seq
            raw=base64.b64decode(obj['data'],validate=True);h.update(raw);size+=len(raw);seq+=1
        elif kind=='end':
            assert obj['name']==current and obj['sha256']==h.hexdigest() and obj['size']==size and obj['chunks']==seq
            inventory[current].update(sha256=h.hexdigest(),chunks=seq,stable=obj['stable']);current=None
        elif kind=='absent':inventory[obj['name']]=dict(status='ABSENT')
        elif kind=='stage':stage=obj
        elif kind=='complete':metrics=obj
assert not pending and current is None
flush()
receipt=json.loads((OUT/'EVIDENCE-export-receipt.json').read_text());assert receipt['exit']==0
assert sum(x['size'] for x in transport.values())==receipt['bytes']['stdout']
index=dict(stage=stage,inventory=inventory,retrieval_metrics=metrics,transport_pins=transport,frames=frames,full_report_reconstruction='Concatenate decoded data in chunk sequence between begin/end; exact original bytes including whitespace.',print_axioms='N/A')
with (OUT/'EVIDENCE-index.json').open('x') as f:json.dump(index,f,indent=2);f.write('\n')
print(json.dumps(dict(files={k:{a:b for a,b in v.items() if a!='pre_stat'} for k,v in inventory.items()},retrieval_metrics=metrics),sort_keys=True))
