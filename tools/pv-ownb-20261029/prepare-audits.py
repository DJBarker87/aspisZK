from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-ownb-20261029'
files=sorted(L.glob('PV_OWNB_*.lean'));roots=[];modules=[];manifest=[]
for p in files:
 if any(x in p.stem for x in ['Audit','Replay']):continue
 s=p.read_text();ns=re.search(r'^namespace (\S+)',s,re.M)[1];th=re.findall(r'^theorem (\w+)',s,re.M)
 roots.extend(ns+'.'+t for t in th);modules.append('R1Z.'+p.stem)
 manifest.append(dict(module='R1Z.'+p.stem,path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip()))
assert roots and len(roots)==len(set(roots))
s=''.join('import '+m+'\n'for m in modules)+'set_option autoImplicit false\n'
s+='\n'.join('#check '+r for r in roots)+'\n'
for r in ['R1Z.PV_OWNB_ActualResult.complete','R1Z.PV_OWNB_SnapshotResult.complete','R1Z.PV_OWNB_LinkCodec.unique','R1Z.PV_OWNB_CursorExit.error_success','R1Z.PV_OWNB_CursorExit.error_failure','R1Z.PV_OWNB_CursorExit.error_divergence','R1Z.PV_OWNB_NoDoubleCleanup.no_second_call']:
 s+='#print '+r+'\n#print axioms '+r+'\n'
(L/'PV_OWNB_StatementsAudit.lean').write_text(s)
(L/'PV_OWNB_AxiomsAudit.lean').write_text('import R1Z.PV_OWNB_StatementsAudit\n'+'\n'.join('#print axioms '+r for r in roots)+'\n')
s='''import R1Z.PV_OWNB_AxiomsAudit
set_option autoImplicit false
namespace R1Z.PV_OWNB_FocusedReplay
open PV_OWNB_Cursor PV_OWN_Link
/-- Frozen model closure replay. No native restoration conclusion is asserted. -/
theorem replay (q : Cursor) (keep : Link → Bool) (h:Valid q) :
 let final:=PV_OWNB_SnapshotFold.run keep (q.length-q.read) q
 Valid final ∧ final.read=q.length ∧
 PV_OWNB_Prefix.values final=PV_OWNB_Prefix.values q++
 (PV_OWNB_ValueFold.input q.source q.read (q.length-q.read)).filter keep :=
 PV_OWNB_SnapshotResult.complete q keep h
#print axioms replay
#print axioms R1Z.PV_OWNB_ActualResult.complete
#print axioms R1Z.PV_OWNB_CursorTransfer.owned
#print axioms R1Z.PV_OWNB_CursorCleanup.positive
#print axioms R1Z.PV_OWNB_NoDoubleCleanup.no_second_call
#print axioms R1Z.PV_OWNB_CleanupRetired.dead
end R1Z.PV_OWNB_FocusedReplay
'''
(L/'PV_OWNB_FocusedReplay.lean').write_text(s)
(E/'frozen-proof-manifest.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),modules=manifest,roots=roots,scope='new model closure; no privacy endpoint/release manifest claim'),indent=2)+'\n')
(E/'audit-targets.txt').write_text('62597 R1Z/PV_OWNB_StatementsAudit\n62598 R1Z/PV_OWNB_AxiomsAudit\n62599 R1Z/PV_OWNB_FocusedReplay\n')
print(len(modules),len(roots))
