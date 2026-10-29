from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-owni-20261029'
files=sorted(p for p in L.glob('PV_OWNI_*.lean') if not any(x in p.name for x in ['Audit','Replay']))
names=[]
for p in files:
 s=p.read_text();ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 for name in re.findall(r'^theorem (\w+)',s,re.M):names.append(ns+'.'+name)
imports=''.join('import R1Z.'+p.stem+'\n' for p in files)
(L/'PV_OWNI_StatementsAudit.lean').write_text(imports+'\n'+''.join('#check @'+n+'\n'for n in names)+''.join('#print '+n+'\n' for n in ['R1Z.PV_OWNI_ScannedResult.result','R1Z.PV_OWNI_InitializedResult.initialized','R1Z.PV_OWNI_Drop.backing','R1Z.PV_OWNI_PublicPlan.same_public','R1Z.PV_OWNI_DensePrune.dense_sparse']))
(L/'PV_OWNI_AxiomsAudit.lean').write_text('import R1Z.PV_OWNI_StatementsAudit\n'+''.join('#print axioms '+n+'\n'for n in names))
(L/'PV_OWNI_FocusedReplay.lean').write_text('''import R1Z.PV_OWNI_AxiomsAudit
set_option autoImplicit false
namespace R1Z.PV_OWNI_FocusedReplay
open Aeneas Aeneas.Std Result PV_OWN_Heap PV_OWNI_RawOps PV_OWNI_Scanner
/-- Focused composition of raw value Result and initialized ownership. This
is not the missing concrete dense/public protocol consuming law. -/
theorem value_and_memory (point column : List Q) (len:point.length=10)
 (m : Memory) (p owner : Nat) (loans:NoLoans m (PV_OWNI_EmptyVec.token m p)) :
 PV_OWNI_RawConsumer.source point column (width point) (trailing point) (suffix point)=
 ok (PV_OWNI_RawConsumer.value point column (width point) (trailing point) (suffix point)) ∧
 PV_OWNC_Vector.Valid PV_OWNI_EntryBytes.codec
  (PV_OWNC_PushFold.append PV_OWNI_EntryBytes.codec
   (PV_OWNI_EmptyVec.buffer m p owner (2^width point))
   ((PV_OWNI_BuildTotal.entries point (width point) (trailing point) (suffix point)).map
    PV_OWNI_NumericBytes.encode)) :=
 ⟨PV_OWNI_ScannedResult.result point column len,
  PV_OWNI_InitializedResult.initialized point p owner m loans⟩
#print axioms value_and_memory
end R1Z.PV_OWNI_FocusedReplay
''')
records=[dict(module='R1Z/'+p.stem,source_path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in files]
(E/'frozen-proof-manifest.json').write_text(json.dumps(dict(development=records,theorems=names,audits=[dict(attempt=64297,module='R1Z/PV_OWNI_StatementsAudit'),dict(attempt=64298,module='R1Z/PV_OWNI_AxiomsAudit'),dict(attempt=64299,module='R1Z/PV_OWNI_FocusedReplay')],scope='one final focused new-source closure replay; not endpoint or release theorem'),indent=2)+'\n')
print(len(files),'development modules',len(names),'named theorems')
