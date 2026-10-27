"""Serial adoption gates. Stop on any comparison disagreement; never time."""
from pathlib import Path
import subprocess,json,shlex,time,sys
D='/home/dombarker/project-offloads/codex-pv-op223-20261027';H='dombarker@100.108.41.90';E=Path('evidence/pv-op223-20261027')
def call(script,args,label):
 for retry in range(10):
  actual=label if retry==0 else label+f'-reservation-{retry+1:02}'
  argv=['python3',D+'/'+script,*[actual if x=='{label}' else x for x in args]]
  with (E/(actual+'-driver.log')).open('w') as out:
   r=subprocess.run(['ssh',H,shlex.join(argv)],stdout=out,stderr=subprocess.STDOUT)
  if r.returncode:
   raw=subprocess.run(['ssh',H,'cat '+D+'/'+actual+'/admission-barrier.json'],capture_output=True,text=True)
   if raw.returncode==0 and not json.loads(raw.stdout)['allowed']:
    (E/(actual+'-barrier-refusal.json')).write_text(json.dumps(dict(raw_exit=r.returncode,classification='reservation refusal; no native command ran',admission=json.loads(raw.stdout)),indent=2)+'\n')
    r.returncode=78
  print(label,actual,'exit',r.returncode,flush=True)
  if r.returncode==78:
   for _ in range(3):print('reservation cooldown: 60 seconds',flush=True);time.sleep(60)
   continue
  if r.returncode:raise SystemExit(r.returncode)
  return actual
 raise SystemExit(78)
labels={}
for mode in (['devnet','pool'] if '--resume-after-default' in sys.argv else ['default','devnet','pool']):
 labels[mode]=call('build.py',['candidate',mode,'{label}'],('build-devnet-public-inputs-002' if mode=='devnet' and '--resume-after-default' in sys.argv else 'build-'+mode))
 # Explicit independent stop, even if the underlying producer's exit behavior changes.
 r=json.loads(subprocess.check_output(['ssh',H,'cat '+D+'/'+labels[mode]+'/comparison.json'],text=True));assert r['matches'],r
for example,label in [('prover_rw_gate','build-fixture'),('prover_rw_differential','build-differential')]:
 labels[label]=call('native.py',['candidate','{label}','cargo','build','--release','-p','aspis-r1-cost-probe','--example',example,'--features','optimized-terminal,r1p-check,ct-host-prover','-j','4','--locked'],label)
 # Stable timing/corpus pin pointer without replacing any receipt or key.
 if labels[label]!=label:
  subprocess.run(['ssh',H,'ln -sfn ../'+labels[label]+' '+D+'/candidate/'+label],check=True)
  if label=='build-differential':
   # Corpus reads one explicit pin path; update the script rather than a comparison.
   p=Path('tools/pv-op223-20261027/corpus.py');s=p.read_text().replace("H/'build-differential/binary-pins.json'","H/'"+labels[label]+"/binary-pins.json'");p.write_text(s)
subprocess.run(['scp','-q','tools/pv-op223-20261027/corpus.py',H+':'+D+'/corpus.py'],check=True)
labels['fixture']=call('native.py',['candidate','{label}',D+'/bin/prover_rw_gate',D+'/fixtures-candidate','0','1'],'fixture-fixed')
r=subprocess.run(['ssh',H,'python3 '+D+'/compare-fixtures.py'],stdout=open(E/'fixture-comparison-driver.log','w'),stderr=subprocess.STDOUT)
if r.returncode:raise SystemExit(r.returncode)
# This is a functional comparison scope; its elapsed times are not a quiet-host timing gate.
labels['corpus']=call('native.py',['candidate','{label}','python3',D+'/corpus.py'],'corpus-paired-1000')
(E/'gate-labels.json').write_text(json.dumps(labels,indent=2)+'\n')
print('All native functional gates passed; quiet timing remains lead-only.',flush=True)
