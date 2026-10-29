"""Recover the missing counterexample from the exact pinned failed GOTO artifact.
No rebuild, renamed harness, changed property, solver timeout, or memory cap.
"""
from pathlib import Path
import json,subprocess,hashlib

def run_trace(B,x,tools):
 old=x['trace_source_attempt'];pins=json.loads((B/(old+'-native-pins.json')).read_text());receipt=json.loads((B/old/'receipt.json').read_text())
 sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
 for n,h in receipt['source_hashes'].items():
  if n.endswith('.rs'):assert sha(B/n)==h,('source changed since failed artifact',n)
 candidates=[p for p in pins if p.endswith('.out') and not p.endswith('.symtab.out')]
 assert len(candidates)==1,candidates
 goto=candidates[0];assert sha(goto)==pins[goto]['sha256']
 cbmc=next(str(p) for p in tools if p.name=='cbmc')
 common=[cbmc,'--no-malloc-may-fail','--no-undefined-shift-check','--no-signed-overflow-check','--nan-check','--no-self-loops-to-assumptions','--no-pointer-primitive-check','--object-bits','16','--unwind','34','--sat-solver','cadical','--slice-formula',goto,'--verbosity','9','--json-ui']
 listed=subprocess.run(common+['--show-properties'],capture_output=True,text=True)
 (B/(x['attempt']+'-properties.json')).write_text(listed.stdout)
 (B/(x['attempt']+'-properties.stderr')).write_text(listed.stderr)
 assert listed.returncode==0,listed.stderr
 data=json.loads(listed.stdout);properties=[p for entry in data for p in entry.get('properties',[])]
 selected=[p for p in properties if 'NEC_decode::post_after' in p.get('description','')]
 assert len(selected)==1,selected
 name=selected[0].get('name') or selected[0]['property']
 command=['timeout','90',*common,'--property',name,'--trace']
 (B/(x['attempt']+'-trace-command.json')).write_text(json.dumps(dict(source_attempt=old,goto=goto,goto_sha256=pins[goto]['sha256'],property=selected[0],command=command,reason='Missing counterexample for completed failing K017; not a timeout rerun or new bridge credit'),indent=1)+'\n')
 return subprocess.run(command,cwd=B).returncode
