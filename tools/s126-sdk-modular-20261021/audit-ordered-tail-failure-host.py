#!/usr/bin/env python3
"""Targeted counterexample investigation; no passing assertion replay/credit."""
from pathlib import Path
import json,subprocess,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-ordered-tail-links-v1-failure-audit';O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_text())
ms=list((H/'target/kani').rglob('aspis_s126_sdk_ordered_tail_links_v1*.kani-metadata.json'));assert len(ms)==1
row=[x for x in load(ms[0])['proof_harnesses'] if x['pretty_name']=='proofs::actual_sdk_finish_drop_chain'][0];program=Path(row['goto_file'].replace('.symtab.out','.out'));tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc')
def run(tag,cmd,high,max_):
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(tag+'-input.json')).write_text(json.dumps(dict(command=cmd,source_sha256=sha(H/'sdk-ordered-tail-links-v1/src/lib.rs'),program_sha256=sha(program),metadata_sha256=sha(ms[0]),runner_sha256=sha(Path(__file__)),qualification=__doc__),indent=2)+'\n')
 return subprocess.call(['systemd-run','--user','--scope','-q','-p',f'MemoryHigh={high}','-p',f'MemoryMax={max_}','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),__doc__,'--',*cmd])
tag='sdk-ordered-tail-links-v1-failure-inventory';assert run(tag,[str(tool),'--show-properties','--json-ui',str(program)],'1G','2G')==0
props=[p for x in load(H/'receipts'/tag/'stdout.log') for p in x.get('properties',[])];wanted=[p for p in props if 'counters[0]' in p['description'] and 'old(' in p['description']];assert wanted
(O/'properties.json').write_text(json.dumps(wanted,indent=2)+'\n')
cmd=['/usr/bin/timeout','180',str(tool),'--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--object-bits','16','--unwind','48','--sat-solver','cadical','--slice-formula','--unwinding-assertions','--trace']
for p in wanted:cmd+=['--property',p['name']]
cmd+=[str(program)];status=run('sdk-ordered-tail-links-v1-failure-trace',cmd,'4G','6G')
(O/'result.json').write_text(json.dumps(dict(exit_status=status,qualification=__doc__,program_sha256=sha(program)),indent=2)+'\n');print(status)
