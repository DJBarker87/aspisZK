import subprocess,json,pathlib,re
E=pathlib.Path(__file__).resolve().parent
pins=json.loads((E/'PINS.json').read_text())['pins']
refs=['codex/cx-prover-rw-20261023','codex/pv-b3p6-20261028','codex/pv-runjoin-20261026','codex/pv-rdcd4-20261029','codex/pv-cblib-20261027','codex/pv-l2b-20261027','codex/pv-l2c-20261028','codex/pv-gate6-20261028']
result={}
for ref in refs:
 rev=pins.get(ref) or subprocess.check_output(['git','rev-parse',ref]).decode().strip();names=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'evidence/','tools/']).decode().splitlines()
 result[ref]={'revision':rev,'files':names}
 print(ref,len(names),sum('receipt' in p and p.endswith('.json') and re.search(r'(kani|/K\d|/k\d)',p,re.I)!=None for p in names))
(E/'TREES.json').write_text(json.dumps(result,indent=2)+'\n')
