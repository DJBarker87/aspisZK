#!/usr/bin/env python3
import hashlib,json,re,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
PACKET=HERE.parent.parent
ROOT=PACKET.parents[2]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
data=json.loads((HERE/'manifest.json').read_text())
rows=[]
for module in sorted({a['module'] for a in data['attempts']}):
    attempts=[a for a in data['attempts'] if a['module']==module]
    last=attempts[-1]
    source=PACKET/'lean'/f'{module}.lean'
    text=source.read_text()
    theorems=re.findall(r'^(?:private )?theorem\s+(\w+)',text,re.M)
    audits=re.findall(r'^#print axioms\s+(\w+)',text,re.M)
    issues=[]
    if last['exit']!=0:issues.append('latest attempt failed')
    if sha(source)!=last['source_sha256']:issues.append('source changed since latest attempt')
    if sorted(theorems)!=sorted(audits):issues.append('theorem audit coverage mismatch')
    if re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',text,re.M):issues.append('forbidden source token')
    for line in last.get('axioms',[]):
        if '[' in line:
            xs=line.split('[',1)[1].split(']',1)[0].split(',')
            if not {x.strip() for x in xs}<={'propext','Classical.choice','Quot.sound'}:issues.append('nonstandard axiom')
    if last['exit']==0:
        obj=Path(last['argv'][last['argv'].index('-o')+1])
        if not obj.exists() or sha(obj)!=last['object_sha256']:issues.append('changed or missing output object')
    for imp in last['direct_imports']:
        if sha(imp['path'])!=imp['sha256']:issues.append('changed direct import '+imp['module'])
    rows.append({'module':module,'attempt':last['attempt'],'theorems':len(theorems),
                 'axiom_audits':len(last.get('axioms',[])),'issues':issues})
accepted=[a for a in data['attempts'] if a.get('final_current') and a['exit']==0]
result={'scope':'focused cached-object proof packet; no frozen release replay',
        'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
        'modules':rows,'attempts':len(data['attempts']),
        'accepted_targets':len(accepted),'accepted_axiom_audits':sum(len(a['axioms']) for a in accepted),
        'accepted_wall_seconds':sum(a['wall_seconds'] for a in accepted),
        'peak_rss_bytes':max(a['peak_rss_bytes'] for a in data['attempts']),
        'swaps':sum(a['swaps'] for a in data['attempts']),
        'passed':all(not r['issues'] for r in rows)}
(HERE/'audit-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
raise SystemExit(0 if result['passed'] else 1)
