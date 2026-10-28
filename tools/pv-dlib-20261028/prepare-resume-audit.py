"""Generate one combined audit and one focused replay from green current sources."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028';root=R/'docs/research/v8-r0-zk-20261009/lean'
passed={}
for p in sorted(E.glob('lean-*/receipt.json')):
 j=json.loads(p.read_text());m=j.get('module','')
 if j.get('exit')==0 and m.startswith('R1Z/PV_DL_') and not any(x in m for x in ['Audit','Replay']):
  q=R/j['source_path']
  if hashlib.sha256(q.read_bytes()).hexdigest()==j['source_sha256']:
   assert 'sorryAx' not in str(j['print_axioms']),m
   passed[m]=j
imports=sorted(passed);checks=[]
for m in imports:
 s=(root/(m+'.lean')).read_text();ns=re.findall(r'^namespace (\S+)',s,re.M)
 for n in re.findall(r'^#print axioms (\S+)',s,re.M):
  if not n.startswith(('R1Z.','PV_DL_')):n=ns[0]+'.'+n
  checks.append(n)
checks=list(dict.fromkeys(checks))
lines=['import '+m.replace('/','.') for m in imports]
lines+=['namespace R1Z.PV_DL_ResumeAudit','set_option autoImplicit false']
lines+=['#print axioms '+n for n in checks]
lines+=['end R1Z.PV_DL_ResumeAudit']
(root/'R1Z/PV_DL_ResumeAudit.lean').write_text('\n'.join(lines)+'\n')
rows=[json.loads((E/r/'status.json').read_text()) for r in ['V201','V187','V231','V234','V235','V236','V237','V238']]
closed=[r for r in rows if r['residual_removed']]
lines=['import R1Z.PV_DL_ResumeAudit','open Aeneas Aeneas.Std Result ProverRwFull','namespace R1Z.PV_DL_ResumeReplay','set_option autoImplicit false',
'''theorem encoder {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (p : aspis_core.r0.domain.Point E) :
    PV_DL_EncoderNative.value inst q p=PV_CB_OwnedEncoder.owned.encoder inst q p :=
  PV_DL_EncoderNative.source_reference inst q p

theorem vector {T : Type} (N : Usize) (v : alloc.vec.Vec T) :
    PV_DL_ArrayNative.reference N v=ok (PV_DL_ArrayOwnership.value N v) :=
  PV_DL_ArrayNative.source_reference N v

theorem sha (compress : PV_DL_ShaFinal.State → List U8 → Result PV_DL_ShaFinal.State)
    (core : PV_DL_ShaFinal.Core) (buffer : Array U8 64#usize) (pos : Usize) (h : pos.val<64) :
    PV_DL_ShaFinal.reference compress core buffer pos=PV_DL_ShaFinal.value compress core buffer pos :=
  PV_DL_ShaFinal.source_reference compress core buffer pos h
''']
lines+=['#print axioms '+r['closing_theorem'] for r in closed]
lines+=['#print axioms encoder','#print axioms vector','#print axioms sha','end R1Z.PV_DL_ResumeReplay']
(root/'R1Z/PV_DL_ResumeReplay.lean').write_text('\n'.join(lines)+'\n')
(E/'resume-audit-roots.json').write_text(json.dumps(dict(imports=imports,checked_declarations=checks,rows_replayed=[r['row'] for r in closed],open_rows=[r['row'] for r in rows if not r['residual_removed']],scope='green current-source matches only; no uncompiled draft and no finite test promoted to theorem'),indent=2)+'\n')
print('combined audit:',len(imports),'modules;',len(checks),'declarations;',len(closed),'native candidate rows')
