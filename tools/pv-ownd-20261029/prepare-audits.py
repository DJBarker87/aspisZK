from pathlib import Path
import re,json,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownd-20261029';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
rows={}
for f in E.glob('lean-*/receipt.json'):
 j=json.loads(f.read_text())
 if j['exit']==0 and j['module'].startswith('R1Z/PV_OWND_'):rows[j['module']]=j
names=[];imports=[]
for module,j in sorted(rows.items()):
 p=R/j['source_path'];b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==j['source_sha256'],module
 imports.append(module.replace('/','.'))
 for name in re.findall(r'^theorem\s+(\w+)',b.decode(),re.M):names.append(module.replace('/','.')+'.'+name)
assert 'R1Z.PV_OWND_ActualInitialized.constructed' in names
header=''.join(f'import {m}\n' for m in imports)+'set_option autoImplicit false\n'
roots=['R1Z.PV_OWND_ActualInitialized.constructed','R1Z.PV_OWND_InitialContext.Context','R1Z.PV_OWND_InitialSuccess.complete','R1Z.PV_OWND_InitialNormal.complete','R1Z.PV_OWND_InitialAbort.null_abort','R1Z.PV_OWND_InitialDrop.complete','R1Z.PV_OWND_CheckSource.scalar_input','R1Z.PV_OWND_InitialProgram.program']
(L/'PV_OWND_StatementsAudit.lean').write_text(header+''.join(f'#check {n}\n' for n in names)+''.join(f'#print {n}\n' for n in roots))
(L/'PV_OWND_AxiomsAudit.lean').write_text(header+''.join(f'#print axioms {n}\n' for n in names))
(L/'PV_OWND_FocusedReplay.lean').write_text('''import R1Z.PV_OWND_ActualInitialized
import R1Z.PV_OWND_InitialNormal
import R1Z.PV_OWND_InitialAbort
import R1Z.PV_OWND_InitialDrop
import R1Z.PV_OWND_CheckSource
set_option autoImplicit false
attribute [local irreducible] R1Z.PV_OWND_ActualBytes.initialized
namespace R1Z.PV_OWND_FocusedReplay
open PV_OWN_Heap PV_OWN_Operations PV_OWNC_Vector PV_OWN_Link PV_W_Threading PV_OWN_Bytes
/-- Focused allocation/stores replay only. It does not assert the native
endpoint-check or complete collector law, which remain outside this root. -/
theorem constructed {S X E : Type}
 (prim : Request → S → Outcome E (Option Nat) × S) (w : State S X)
 (owner p : Nat) (s : S) (payload : Nat → Link → Bytes)
 (ctx:PV_OWND_InitialContext.Context prim w owner)
 (h:prim ⟨1016,2⟩ w.allocator=(.ok (some p),s))
 (agrees:∀ i v, PV_OWNB_Padding.Agrees (PV_OWNB_LinkBytes.encode v) (payload i v))
 (oom : Action S X E (Buffer Link)) :
 let r:=PV_OWND_InitialRun.construct prim owner oom payload w
 ∃ b, r.outcome=.ok b ∧ PV_OWNC_Vector.Valid PV_OWNB_LinkCodec.codec b ∧
 b.length=127 ∧ b.capacity=127 ∧ r.world.memory=b.memory ∧ r.world.allocator=s ∧
 r.world.extra=w.extra ∧ r.calls=[(w,.allocate 1016 2)] := by
 dsimp only
 rw [PV_OWND_InitialSuccess.complete prim owner p oom payload w s h]
 have hb:=PV_OWND_ActualInitialized.constructed prim w owner p s payload ctx h agrees
 refine ⟨_,rfl,hb.1,hb.2.1,hb.2.2.1,rfl,?_,rfl,rfl⟩
 simp only [allocate,emit,h]
#print axioms constructed
end R1Z.PV_OWND_FocusedReplay
''')
(E/'frozen-proof-manifest.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),modules=imports,theorems=names,roots=roots,purpose='one new initial-source model closure; not collector or privacy endpoint release replay'),indent=2)+'\n')
print(len(imports),'modules',len(names),'theorems')
