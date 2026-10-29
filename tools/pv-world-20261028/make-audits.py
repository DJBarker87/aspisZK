"""Emit the final focused-frontier axioms audit and import replay.
This is not the frozen deployment manifest or a privacy release theorem.
"""
from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-world-20261028'
exclude={'PV_W_FinalAudit','PV_W_CarrierObstruction','PV_W_ResumeAudit','PV_W_ResumeReplay'}
files=[p for p in sorted(L.glob('PV_W_*.lean')) if p.stem not in exclude]
commands=[];pins=[]
for p in files:
 s=p.read_text();ns=re.search(r'^namespace\s+(\S+)',s,re.M)
 names=re.findall(r'^theorem\s+(\w+)',s,re.M)
 if names:assert ns,p
 commands += ['#print axioms '+ns[1]+'.'+n for n in names]
 pins.append(dict(module='R1Z.'+p.stem,path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],cwd=R,text=True).strip()))
imports=['import R1Z.'+p.stem for p in files]
imports+=['import R1Z.PV_RunJoin_NativeEffectTransport','import R1Z.PV_RunJoin_OsWorldFrames']
(L/'PV_W_ResumeAudit.lean').write_text('\n'.join(imports)+'\nset_option autoImplicit false\n\n/- Focused model/source frontier only; native/deployment target remains open. -/\n'+'\n'.join(commands)+'\n')
(L/'PV_W_ResumeReplay.lean').write_text('''import R1Z.PV_W_ResumeAudit
set_option autoImplicit false
/- One final focused import/axioms replay. No frozen deployment manifest claim. -/
#check R1Z.PV_RunJoin_NativeEffectInterface.Identity
#check R1Z.PV_RunJoin_NativeEffectTransport.permitted
#print axioms R1Z.PV_W_Enriched.witness_representable
#print axioms R1Z.PV_W_ReservationThreading.source_complete
#print axioms R1Z.PV_W_TypedThreading.reservation_threads
#print axioms R1Z.PV_W_EntryThreading.entry_source
#print axioms R1Z.PV_W_OsCombined.reservation_os
#print axioms R1Z.PV_W_RepeatFile.repeated_exact
''')
(E/'resume-source-freeze.json').write_text(json.dumps(dict(scope='focused model/source frontier; no native/deployment instance',sources=pins,axioms_queries=len(commands)),indent=2)+'\n')
print('Focused audit:',len(files),'modules,',len(commands),'explicit theorem queries')
