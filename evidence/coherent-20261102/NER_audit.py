"""Audit the already rebuilt coherent cohort; never recompile a model module."""
import hashlib,json,subprocess,sys
from pathlib import Path
B=Path(__file__).resolve().parent
pins=[json.loads(l) for l in (B/'NER_PREAGG_OBJECTS_A901.jsonl').read_text().splitlines()]
def verify():
 for module in pins:
  for artifact in module['artifacts']:
   h=hashlib.sha256()
   with Path(artifact['path']).open('rb') as f:
    for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
   assert h.hexdigest()==artifact['sha256'],artifact['path']
verify();print('NER_PREAGG_PINS_VERIFIED',flush=True)
cmd=['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','env','lean','-j1','-M15000','-DElab.async=false','--run','NER_FinalDriverV2.lean','final']
r=subprocess.run(cmd)
verify();print('NER_POSTAGG_INPUTS_UNCHANGED',flush=True)
sys.exit(r.returncode)
