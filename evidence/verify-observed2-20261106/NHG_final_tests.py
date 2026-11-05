from pathlib import Path
import json,importlib.util,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;spec=importlib.util.spec_from_file_location('NHG_final',E/'NHG_final_validate.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
results=[]
def mutate(name,file,change,jsonl=False):
 p=E/file;raw=p.read_bytes()
 try:
  x=[json.loads(l)for l in raw.splitlines()]if jsonl else json.loads(raw);change(x);p.write_text(''.join(json.dumps(r)+'\n'for r in x)if jsonl else json.dumps(x))
  try:v.validate()
  except (AssertionError,KeyError,ValueError,StopIteration):results.append(dict(name=name,rejected=True));return
  raise RuntimeError('Mutation accepted: '+name)
 finally:p.write_bytes(raw)
mutate('no claims promotion','NHG_CLOSED.json',lambda x:x['functions'].append(dict(rows=['TX1:129'],status='CLOSED')))
mutate('new root must have standard axioms','NHG_audit/batch11/proof11.json',lambda x:x['results'][0].update(walked_axioms=['sorryAx']))
mutate('final scan duplicate rejected','NHG_LOADED_scan.jsonl',lambda x:x[-1].update(duplicate_owners=['bad']),True)
mutate('full budget trace required','NHG_ATTEMPTS.jsonl',lambda x:x.pop(),True)
mutate('packaging cannot claim proof run','NHG_EXPORT.json',lambda x:x.update(formal_tool_invocations=1))
mutate('retained cache cannot disappear','NHG_EXPORT.json',lambda x:x.update(cache_deleted=True))
mutate('binary pin must match','NHG_EXPORT.json',lambda x:x['exported_files']['bin/NHG_Driver'].update(sha256='0'*64))
mutate('failed final joint denied','NHG_L088/receipt.json',lambda x:x.update(exit_status=1))
assert v.validate()['final_status']=='PASS';(E/'NHG_FINAL_MUTATIONS.json').write_text(json.dumps(results,indent=1)+'\n');print(len(results),'final denial controls rejected')
