from pathlib import Path
import subprocess, sys

repo=Path(__file__).resolve().parents[1]
label=sys.argv[1]
assert label.replace('-','').isalnum()
source=repo/'docs/research/100bit-spend-path-20261013/lean/ExtractedQM31SamplerCorrect.lean'
saved=repo/'.j1-r18-sampler/correct/attempt-sources'; saved.mkdir(exist_ok=True)
candidate=saved/(label+'.lean'); assert not candidate.exists()
candidate.write_bytes(source.read_bytes())
host='dombarker@100.108.41.90'
work='/home/dombarker/project-offloads/aspis-r1-r18-sampler-20261016/correct'
subprocess.run(['scp',str(source),host+':'+work+'/sources/ExtractedQM31SamplerCorrect.lean'],check=True)
code='''from pathlib import Path
import hashlib,json,subprocess
w=Path(WORK)
p=w/'sources/SOURCE-MANIFEST.json'
m=json.loads(p.read_text())
m['modules']['ExtractedQM31SamplerCorrect']['source_sha256']=hashlib.sha256((p.parent/'ExtractedQM31SamplerCorrect.lean').read_bytes()).hexdigest()
p.write_text(json.dumps(m,indent=2)+'\\n')
raise SystemExit(subprocess.run(['systemd-run','--user','--scope','--unit=aspis-r18-c-'+LABEL+'-20261016','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','python3',str(w/'runner.py'),'run',str(w),'--target','ExtractedQM31SamplerCorrect','--external-snapshot',str(w/'external-inputs-correct.json'),'--attempt',LABEL,'--revision','fe98214e32fa777b11712f9905a4ac4db0d2488d']).returncode)
'''.replace('WORK',repr(work)).replace('LABEL',repr(label))
raise SystemExit(subprocess.run(['ssh',host,'python3','-'],input=code,text=True).returncode)
