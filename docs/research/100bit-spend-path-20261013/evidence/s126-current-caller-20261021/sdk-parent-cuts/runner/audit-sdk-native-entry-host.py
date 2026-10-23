#!/usr/bin/env python3
"""Audit the checked pre-comparison cut's marker, call replacement and scope.
Metadata only; this does not prove actual comparison or verifier-entry transport.
"""
from pathlib import Path
import hashlib,json,subprocess,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
tag='sdk-native-entry-audit-v1';checked='sdk-native-entry-cut-v2'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inp=H/(checked+'-input.json');data=json.loads(inp.read_text())
program=H/checked/'ready.out';tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/goto-instrument')
if 'run' not in sys.argv:
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',proof_input_sha256=sha(inp),program_sha256=sha(program),tool_sha256=sha(tool),runner_sha256=sha(Path(__file__)),qualification=__doc__),indent=2)+'\n')
 raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Inspect retained checked entry cut marker and call replacement; no solver replay','--','python3',__file__,'run']))
receipt=H/'receipts'/checked/'receipt.json';r=json.loads(receipt.read_text())
assert r['exit_status']==10 and r['swaps']==0
text=subprocess.check_output([str(tool),'--show-symbol-table',str(program)],text=True)
blocks=text.split('Symbol......: ')[1:]
marker=[b for b in blocks if b.splitlines()[0]==data['marker_symbol']]
assert len(marker)==1
assert 'unsigned long int' in marker[0] and '{ 1, 0, 0, 0, 0, 0, 165, 81 }' in marker[0]
body=H/checked/'entry-cut-body.c';declaration=H/checked/'entry-cut-declaration.c'
assert sha(body)==data['tool_pins'][str(body)] and sha(declaration)==data['tool_pins'][str(declaration)]
assert 'if(n==688){'+data['marker_symbol']+'+=1;return 1;}' in body.read_text()
assert 'return memcmp(a,b,n);' in body.read_text()
cmds=data['commands'];replace=next(i for i,c in enumerate(cmds) if '--replace-calls' in c)
append=next(i for i,c in enumerate(cmds) if str(body) in c)
assert replace<append and cmds[replace][cmds[replace].index('--replace-calls')+1]=='memcmp:s126_entry_memcmp'
props=json.loads((H/checked/'properties-without-traces.json').read_text())
noncover=[p for p in props if p['sourceLocation'].get('propertyClass')!='cover']
covers=[p for p in props if p['sourceLocation'].get('propertyClass')=='cover']
assert len(noncover)==2515 and all(p['status']=='SUCCESS' for p in noncover)
assert len(covers)==3 and all(p['status']=='FAILURE' for p in covers)
out=dict(schema='focused-extractor-proof-packet-v1',program_sha256=sha(program),proof_input_sha256=sha(inp),proof_receipt_sha256=sha(receipt),marker=marker[0],body_sha256=sha(body),declaration_sha256=sha(declaration),replace_command_index=replace,append_body_command_index=append,noncover_successes=len(noncover),reachable_covers=len(covers),qualification='Pre-comparison entry only. All688-byte memcmp calls mark entry and return1. Other comparisons forward to the original model because replacement precedes body append. The inherited lamport cover caption mentions verifier entry; its actual predicate is the comparison marker. Neither original comparison correctness nor first-entry linkage follows from this cut. Native body/helper prefix unchanged; concrete child installation and general heap/caller transport remain open.')
(H/'receipts'/tag/'entry-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(noncover_successes=len(noncover),reachable_covers=len(covers),scope='comparison entry only')))
