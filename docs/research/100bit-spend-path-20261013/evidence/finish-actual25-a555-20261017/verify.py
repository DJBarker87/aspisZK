#!/usr/bin/env python3
"""Read/hash and exact identifier-binding replay only; no Lean or extractor."""
from pathlib import Path
import json,tarfile,hashlib,tempfile,subprocess,sys
E=Path(__file__).resolve().parent;B=E.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest();m=json.loads((E/'manifest.json').read_text());archive=E/m['archive'];assert sha(archive.read_bytes())==m['archive_sha256']
with tarfile.open(archive) as t:
 sums=json.load(t.extractfile('SHA256SUMS.json'));assert len(t.getmembers())==len(sums)+1==m['members'];fs={n:t.extractfile(n).read() for n in sums}
 for n,b in fs.items():assert sha(b)==sums[n],n
 records={Path(n).stem:json.loads(b) for n,b in fs.items() if n.startswith('successful-targets/')};assert len(records)==3;count=0
 for n,d in records.items():
  assert d['exit_status']==0 and d['axioms']['passed'] and d['process_swaps']==0 and d['cgroup_swap_current']=='0'
  assert d['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
  assert sha(fs['sources/'+n+'.lean'])==d['key']['source_sha256'];assert sha(fs['objects/'+n+'.olean'])==d['objects']['.olean']['sha256']
  assert fs['sources/'+n+'.lean']==(B/'lean/bridge-finish-a555-20261017'/(n+'.lean')).read_bytes()
  for dep,pin in d['key']['imports'].items():
   if dep in records:assert pin['receipt_key']==sha(json.dumps(records[dep]['key'],sort_keys=True).encode()) and pin['objects']==records[dep]['objects']
  for r in d['axioms']['reports']:assert set(r['axioms'])<={'propext','Classical.choice','Quot.sound'};count+=1
 assert count==19
 assert fs['binding-audit.json']==(B/'lean/bridge-finish-a555-20261017/binding-audit.json').read_bytes()
 audit=json.loads(fs['binding-audit.json']);assert audit['chunk_parser']=='include_impl_def' and len(audit['exact_body_audits'])==14 and len(audit['fixed_round_body_token_identity'])==5 and len(audit['canonical_function_token_identity'])==7
 assert sha(fs['fixed-rounds-generated/Funs.lean'])==audit['accepted_rounds_raw_funs_sha256']
 with tempfile.TemporaryDirectory() as tmp:
  w=Path(tmp)
  for part,names in [('raw',['Types.lean','Funs.lean']),('rounds',['Types.lean','Funs.lean'])]:
   (w/part).mkdir()
   for n in names:(w/part/n).write_bytes(fs[('finish-extraction/generated/AspisR1PublicPreparation/' if part=='raw' else 'fixed-rounds-generated/')+n])
  model=w/'ExtractedSemanticRoundsModel.lean';model.write_bytes(fs['rounds-predecessor/sources/ExtractedSemanticRoundsModel.lean'])
  subprocess.run([sys.executable,str(B/'tools/finish-caller-kit/bind.py'),'--generated',str(w/'raw'),'--round-generated',str(w/'rounds'),'--round-model',str(model),'--out',str(w/'bound')],check=True,stdout=subprocess.DEVNULL)
  assert (w/'bound/ExtractedVerifyFinishModel.lean').read_bytes()==fs['sources/ExtractedVerifyFinishModel.lean']
  assert (w/'bound/binding-audit.json').read_bytes()==fs['binding-audit.json']
 print('PASS3coherent targets;19standard reports;14exact bodies;5fixed round body identities;7canonical helpers; full actual-first source25/typed decoding')
