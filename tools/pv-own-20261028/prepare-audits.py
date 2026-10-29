from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-own-20261028'
files=sorted(p for p in L.glob('PV_OWN_*.lean') if p.stem not in ['PV_OWN_StatementsAudit','PV_OWN_AxiomsAudit','PV_OWN_FocusedReplay'])
queries=[];pins=[]
for p in files:
 s=p.read_text();ns=''
 for line in s.splitlines():
  if line.startswith('namespace '):ns=line.split()[1]
  match=re.match(r'^theorem (\w+)',line)
  if match:queries.append(ns+'.'+match[1])
 if p.stem in ['PV_OWN_U8','PV_OWN_U16']:queries.append(ns+'.codec')
 pins.append(dict(module='R1Z/'+p.stem,path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip()))
imports='\n'.join('import R1Z.'+p.stem for p in files)+'\n'
statements=imports+'\n'.join('#check '+q for q in queries)+'\n'
for q in ['R1Z.PV_OWN_CheckedAlloc.owned_success','R1Z.PV_OWN_CheckedStore.representation','R1Z.PV_OWN_CollectorFrame.unread','R1Z.PV_OWN_Reserve.typed_prefix','R1Z.PV_OWN_Unique.move_preserves','R1Z.PV_OWN_Containers.utf8']:
 statements+='#print '+q+'\n#print axioms '+q+'\n'
(L/'PV_OWN_StatementsAudit.lean').write_text(statements)
(L/'PV_OWN_AxiomsAudit.lean').write_text('import R1Z.PV_OWN_StatementsAudit\n'+'\n'.join('#print axioms '+q for q in queries)+'\n')
(L/'PV_OWN_FocusedReplay.lean').write_text('''import R1Z.PV_OWN_AxiomsAudit
set_option autoImplicit false
namespace R1Z.PV_OWN_FocusedReplay
open PV_OWN_Heap PV_OWN_View PV_OWN_Bytes
/-- Focused replay of the checked interface, not a native consumer restoration. -/
theorem checked_store {T : Type} (codec : Codec T) (m : Memory)
 (cmd : PV_OWN_CheckedStore.Command codec m) :
 View codec (PV_OWN_CheckedStore.execute cmd) cmd.token cmd.offset cmd.value ∧
 Writable (PV_OWN_CheckedStore.execute cmd) cmd.owner cmd.token
  (store cmd.cell cmd.offset codec.width (codec.encode cmd.value)) := by
 constructor
 · exact PV_OWN_CheckedStore.representation cmd
 · exact PV_OWN_Laws.InitWritable codec cmd.token cmd.cell cmd.owner cmd.offset cmd.value m cmd.writable
#print checked_store
#print axioms checked_store
#print axioms PV_OWN_Reserve.complete
#print axioms PV_OWN_Reserve.typed_prefix
#print axioms PV_OWN_CollectorFrame.unread
#print axioms PV_OWN_Containers.zero_capacity
end R1Z.PV_OWN_FocusedReplay
''')
(E/'frozen-proof-manifest.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),modules=pins,queries=queries,scope='shared model interface only; not the privacy endpoint or native consumer closure'),indent=2)+'\n')
print('modules',len(pins),'queries',len(queries))
