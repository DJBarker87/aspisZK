"""Retarget fresh NHR bodies using NHL's reviewed nominal/constant substitution.
No extraction, callee output law, or native credit is produced by this script.
"""
from pathlib import Path
import json,hashlib,re,sys,difflib
E=Path(__file__).resolve().parent;R=E.parent/'extract-stage-20261106';L=E.parent/'prepare-emit-20261106'
records=[]
for function,title in [('prepare','Prepare'),('tx1','Tx1')]:
 raw=R/'NHR_lean'/('NHR_'+function)/'Funs.lean';s=raw.read_text()
 body=s[s.index('def verifier.candidate.'+function+'\n'):s.index('\nend NHR_'+function)]
 params=json.loads((raw.parent/'NHR_PARAMETERS.json').read_text())
 mapping=json.loads((L/('NHL_RETARGET_'+function.upper()+'.json')).read_text())['mapping']
 if function=='prepare':
  body=body.replace('def verifier.candidate.prepare\n','def prepare (ops : AspisR1CurrentCaller.Ops)\n',1)
 else:
  body=body.replace('def verifier.candidate.tx1\n  {H : Type}','def tx1 (ops : AspisR1CurrentCaller.Ops)\n  {H : Type} (prepareCall : Prepare H)',1)
 for p in params:
  generated=p['generated_name'];replacement=mapping.get(generated,generated)
  # None observation is the deployed instantiation; mark stays the canonical source function.
  if generated=='verifier.mark':replacement='verifier.mark'
  body=re.sub(r'(?<![\w.])'+re.escape(p['parameter'])+r'(?![\w.])',replacement,body)
 # Longer names first avoids remapping the result of another substitution.
 for a,b in sorted(mapping.items(),key=lambda kv:-len(kv[0])):
  # params have already been substituted and are excluded from this pass.
  if a in [p['generated_name'] for p in params]:continue
  body=body.replace(a,b)
 old=(L/('NHL_Emitted'+title+'.lean')).read_text()
 header=old[:old.index('def '+function+' (ops')]
 header=header.replace('NHL_Emitted'+title,'NHW_Emitted'+title)
 if function=='tx1':header=header.replace('import NHL_EmittedPrepare','import NHW_EmittedPrepare')
 output=header+body+'\nend AspisR1.NHW_Emitted'+title+'\n'
 p=E/('NHW_Emitted'+title+'.lean')
 if '--check' in sys.argv:assert p.read_text()==output,p
 else:p.write_text(output)
 diff=''.join(difflib.unified_diff(old.splitlines(True),output.splitlines(True),fromfile='NHL_Emitted'+title+'.lean',tofile=p.name))
 if '--check' not in sys.argv:E.joinpath('NHW_'+function+'_vs_NHL.diff').write_text(diff)
 records.append(dict(function=function,input=str(raw.relative_to(E.parent.parent)),sha256=hashlib.sha256(raw.read_bytes()).hexdigest(),parameters=params,mapping=mapping,output=p.name,output_sha256=hashlib.sha256(output.encode()).hexdigest(),body_sha256=hashlib.sha256(body.encode()).hexdigest()))
if '--check' in sys.argv:assert json.loads((E/'NHW_RETARGET.json').read_text())==records
else:(E/'NHW_RETARGET.json').write_text(json.dumps(records,indent=1)+'\n')
print('NHR retarget checked' if '--check' in sys.argv else 'NHR bodies retargeted')
