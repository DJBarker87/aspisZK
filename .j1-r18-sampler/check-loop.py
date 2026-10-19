from pathlib import Path
import json,subprocess,sys
repo=Path(__file__).resolve().parents[1]
label=sys.argv[1]
assert label.replace('-','').isalnum()
source=repo/'docs/research/100bit-spend-path-20261013/lean/ExtractedQM31SamplerPassLoop.lean'
saved=repo/'.j1-r18-sampler/pass-attempt-sources';saved.mkdir(exist_ok=True)
(saved/(label+'.lean')).write_bytes(source.read_bytes())
host='dombarker@100.108.41.90';work='/home/dombarker/project-offloads/aspis-r1-r18-sampler-20261016/pass'
subprocess.run(['scp',str(source),host+':'+work+'/sources/ExtractedQM31SamplerPassLoop.lean'],check=True)
code='''from pathlib import Path
import hashlib,json,subprocess
w=Path(WORK)
p=w/'sources/SOURCE-MANIFEST.json'
m=json.loads(p.read_text());m['modules']['ExtractedQM31SamplerPassLoop']={'source':'docs/research/100bit-spend-path-20261013/lean/ExtractedQM31SamplerPassLoop.lean','stage_as':'ExtractedQM31SamplerPassLoop.lean','source_revision':'eec65922001d1efbda31e0a21ada36d3cd47634a plus new proof','source_sha256':hashlib.sha256((p.parent/'ExtractedQM31SamplerPassLoop.lean').read_bytes()).hexdigest(),'imports':['ExtractedQM31SamplerPass'],'role':'Actual complete descending loop correspondence','axiom_requests':5};m['topological_order']=['ExtractedQM31SamplerPass','ExtractedQM31SamplerPassLoop'];p.write_text(json.dumps(m,indent=2)+'\\n')
raise SystemExit(subprocess.run(['systemd-run','--user','--scope','--unit=aspis-r18-c-'+LABEL+'-20261016','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','python3',str(w/'runner.py'),'run',str(w),'--target','ExtractedQM31SamplerPassLoop','--external-snapshot',str(w/'external-inputs-pass.json'),'--attempt',LABEL,'--revision','c6bc7dff9961632c60676d32f349ba2ccce39614']).returncode)
'''.replace('WORK',repr(work)).replace('LABEL',repr(label))
raise SystemExit(subprocess.run(['ssh',host,'python3','-'],input=code,text=True).returncode)
