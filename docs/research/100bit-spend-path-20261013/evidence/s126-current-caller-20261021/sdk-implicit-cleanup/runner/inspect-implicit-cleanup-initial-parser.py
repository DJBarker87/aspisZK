#!/usr/bin/env python3
"""Inspect the actual implicit-cleanup function order, no solver replay."""
from pathlib import Path
import json,hashlib,subprocess,sys,tomllib,re
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');version=sys.argv[1];tag='sdk-'+version+'-order-v1';P=H/('sdk-'+version);load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
crate=tomllib.loads((P/'Cargo.toml').read_text())['package']['name'].replace('-','_');matches=list((H/'target/kani').rglob(crate+'*.kani-metadata.json'));assert len(matches)==1
metadata=load(matches[0]);h=next(h for h in metadata['proof_harnesses'] if h['pretty_name']=='proofs::actual_sdk_ordered_cleanup');raw=Path(h['goto_file']);program=Path(str(raw).replace('.symtab.out','.out'));tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/goto-instrument');cmd=[str(tool),'--show-goto-functions',str(program)]
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(command=cmd,program_sha256=sha(program),raw_goto_sha256=sha(raw),source_sha256=sha(P/'src/lib.rs'),tool_sha256=sha(tool),runner_sha256=sha(Path(__file__))),indent=2)+'\n')
s=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),__doc__,'--',*cmd]);assert s==0
rows=(H/'receipts'/tag/'stdout.log').read_text().splitlines();a=next(i for i,s in enumerate(rows) if s.startswith('proofs::implicit_cleanup /*'));b=next(i for i in range(a+1,len(rows)) if rows[i].startswith('^^^^^^^^'));fragment='\n'.join(rows[a:b])+'\n';calls=[re.sub(r'^\s*(?:\d+:\s*)?','',line) for line in rows[a:b] if re.match(r'^\s*(?:\d+:\s*)?CALL ',line)]
copy='copy-cleanup' in version
if copy:
 assert 'copy_from_slice' in calls[0];drops=calls[1:]
else:drops=calls
assert len(drops)==5,calls
roles=[]
for line in drops:
 assert 'drop_in_place' in line,line
 m=re.search(r'implicit_cleanup::([a-z_]+)\)\)$',line);assert m,line;roles.append(m[1])
assert roles==['reply','proof','statement','public','checkpoint'],roles
for line,typ in zip(drops,['alloc3vec3Vech','4cell3RefQSh','PoolV1PairForestTerminalStatementV1','4cell3RefQSh','4cell6RefMutQSh']):assert typ in line,line
O=H/(tag+'-export');O.mkdir(exist_ok=False);(O/'implicit-cleanup-goto.txt').write_text(fragment);(O/'certificate.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',roles=roles,calls=calls,fragment_sha256=sha(O/'implicit-cleanup-goto.txt'),source_sha256=sha(P/'src/lib.rs'),program_sha256=sha(program),raw_goto_sha256=sha(raw),runner_sha256=sha(Path(__file__)),qualification='Exact actual implicit cleanup role/type order matches frozen native stage1 normal post-copy suffix. Host source/ABI/deallocator interpretation and full caller composition remain.'),indent=2)+'\n');print(json.dumps(dict(output=str(O),roles=roles,calls=len(calls))))
