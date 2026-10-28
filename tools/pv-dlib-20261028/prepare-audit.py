from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028';root=R/'docs/research/v8-r0-zk-20261009/lean'
passed={}
for p in E.glob('lean-*/receipt.json'):
 j=json.loads(p.read_text());m=j.get('module','')
 if j.get('exit')==0 and m.startswith('R1Z/PV_DL_'):
  q=R/j['source_path']
  if hashlib.sha256(q.read_bytes()).hexdigest()==j['source_sha256']:passed[m]=j
imports=sorted(passed)
lines=['import '+m.replace('/','.') for m in imports]
lines+=['open Aeneas Aeneas.Std Result','namespace R1Z.PV_DL_Audit','set_option autoImplicit false', '''theorem unit_run {B : Type} (events : List B) :
    PV_DL_CompressionTrace.run (fun (_ : Unit) (_ : B) => ok ()) events ()=ok () := by
  induction events with
  | nil => rfl
  | cons b tail ih => simp only [PV_DL_CompressionTrace.run,bind_tc_ok,ih]

theorem padding_success (buffer : Array U8 64#usize) (pos : Usize)
    (suffix : Array U8 8#usize) (h : pos.val<64) :
    PV_DL_FinalizeParam.reference (fun (_ : Unit) (_ : List U8) => ok ()) () buffer pos suffix=
      ok ((),PV_CBL_PaddingModel.first buffer.val pos.val suffix.val,0) := by
  rw [PV_DL_FinalizeParam.source _ _ buffer pos suffix h]
  simp only [PV_DL_FinalizeParam.model,unit_run,bind_tc_ok]

theorem padding_domain : ∃ buffer : Array U8 64#usize, ∃ pos : Usize,
    ∃ suffix : Array U8 8#usize, pos.val<64 ∧
    PV_DL_FinalizeParam.reference (fun (_ : Unit) (_ : List U8) => ok ()) () buffer pos suffix=
      ok ((),PV_CBL_PaddingModel.first buffer.val pos.val suffix.val,0) :=
  ⟨Array.repeat 64#usize 0#u8,0#usize,Array.repeat 8#usize 0#u8,by decide,
    padding_success _ _ _ (by decide)⟩
''']
# Audit the complete recorded public surfaces of all successful new modules.
checks=[]
for m in imports:
 s=(root/(m+'.lean')).read_text()
 ns=re.findall(r'^namespace (\S+)',s,re.M)
 # Own extracted modules use their generated namespace; others one qualified namespace.
 for n in re.findall(r'^#print axioms (\S+)',s,re.M):
  if '.' not in n or not n.startswith(('R1Z.','PV_DL_')):n=ns[0]+'.'+n
  checks.append(n)
lines+=['#print axioms '+n for n in dict.fromkeys(checks)]
lines+=['#print axioms unit_run','#print axioms padding_success','#print axioms padding_domain','end R1Z.PV_DL_Audit']
(root/'R1Z/PV_DL_Audit.lean').write_text('\n'.join(lines)+'\n')
(E/'audit-roots.json').write_text(json.dumps(dict(imports=imports,checked_declarations=list(dict.fromkeys(checks)),source='successful current-source matches only; uncompiled drafts excluded'),indent=2)+'\n')
print('audit',len(imports),'modules',len(checks),'declarations')
