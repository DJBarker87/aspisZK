#!/usr/bin/env python3
"""Source-only observer/ghost emission audit of the unseeded native context.
This is an emission audit, not a proof of the complete caller.
"""
from pathlib import Path
import json,hashlib,subprocess,sys,re
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
tag='sdk-native-unseeded-observer-emission-properties-v1';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pin=H/'sdk-native-context-check-v13-input.json';data=json.loads(pin.read_text());prepared=Path(data['commands'][0][3]);raw=Path(str(prepared).replace('.out','.symtab.out'));tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/goto-instrument')
assert sha(prepared)==data['input_goto_sha256']
if 'run' not in sys.argv:
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 (H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',raw_goto_sha256=sha(raw),native_input_sha256=sha(pin),prepared_sha256=sha(prepared),tool_sha256=sha(tool),runner_sha256=sha(Path(__file__)),qualification=__doc__),indent=2)+'\n')
 raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Read raw native observer constant/global references; no solver replay','--','python3',__file__,'run']))
text=subprocess.check_output([str(tool),'--show-symbol-table',str(raw)],text=True)
blocks=text.split('Symbol......: ')[1:];observers=[]
for block in blocks:
 if block.splitlines()[0].endswith('8observer'):
  assert 'proofs' not in block
  observers.append(block)
assert len(observers)==1
targets=[re.search(r'&([A-Za-z0-9_$]+)\);',x)[1] for x in observers]
assert '$$global$$' in targets[0]
constant=[b for b in blocks if b.splitlines()[0].replace('::','$$').replace('.','_')==targets[0]];assert len(constant)==1
assert '{ 0, 0, 0, 0, 0, 0, 0, 0 }' in constant[0]
assert 'Type........: const struct ' in constant[0]
out=H/'receipts'/tag/'emission-audit.json'
out.write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',raw_goto_sha256=sha(raw),observers=observers,constant=constant[0],qualification=__doc__),indent=2)+'\n')
print(json.dumps(dict(observer_functions=1,constant=targets[0],raw_goto_sha256=sha(raw))))
