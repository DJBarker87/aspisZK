from pathlib import Path
import re
L=Path('lean');types=(L/'NCX_Reference/Types.lean').read_text()
enums={n:re.findall(r'^\| (\w+)',types.split('inductive '+n+' where')[1].split('/--')[0],re.M) for n in ['VerifierEntryStatusV1','PoolV1VerifierRegistryFormatError']}
s='import NCX_Reference.Funs\nimport AdapterRwModel\nset_option autoImplicit false\nnamespace NCX_Carrier\nopen Aeneas Aeneas.Std Result\nopen AdapterRw.aspis_statement.pool_v1.verifier_registry\n'
for name,key in [('VerifierEntryStatusV1','status'),('PoolV1VerifierRegistryFormatError','error')]:
 s+=f'\ndef {key} : NCX_Reference.{name} → {name}\n'+''.join(f'  | .{c} => .{c}\n' for c in enums[name])
 s+=f'\ndef from_{key} : {name} → NCX_Reference.{name}\n'+''.join(f'  | .{c} => .{c}\n' for c in enums[name])
for name,key in [('VerifierRegistryV2','registry'),('VerifierRegistryEntryV2','entry')]:
 fields=re.findall(r'^  (\w+) :',types.split('structure '+name+' where')[1].split('/--')[0],re.M)
 s+=f'\ndef {key} (v : NCX_Reference.{name}) : {name} :=\n  ⟨'+','.join(('status v.status' if f=='status' else 'v.'+f) for f in fields)+'⟩\n'
 s+=f'\ndef from_{key} (v : {name}) : NCX_Reference.{name} :=\n  ⟨'+','.join(('from_status v.status' if f=='status' else 'v.'+f) for f in fields)+'⟩\n'
for name,key in [('VerifierEntryStatusV1','status'),('PoolV1VerifierRegistryFormatError','error'),('VerifierRegistryV2','registry'),('VerifierRegistryEntryV2','entry')]:
 for reverse in [False,True]:
  ty=name if reverse else 'NCX_Reference.'+name
  expr=f'{key} (from_{key} v)' if reverse else f'from_{key} ({key} v)'
  thm=f'{key}_'+('surjective' if reverse else 'roundtrip')
  proof='cases v <;> rfl' if key!='entry' else 'cases v with | mk st _ _ _ _ _ _ _ _ _ _ _ _ _ _ => cases st <;> rfl'
  s+=f'\ntheorem {thm} (v : {ty}) : {expr}=v := by\n  {proof}\n#print axioms {thm}\n'
s+='end NCX_Carrier\n';(L/'NCX_Carrier.lean').write_text(s)
s='''import NCX_Carrier
import NCV_InstallationSupport
set_option autoImplicit false
noncomputable section
namespace NCX_Install
open Aeneas Aeneas.Std Result AspisR1

def mapReturn {A B : Type} (f : A → B) : core.result.Result A NCX_Reference.PoolV1VerifierRegistryFormatError →
    core.result.Result B AdapterRw.aspis_statement.pool_v1.verifier_registry.PoolV1VerifierRegistryFormatError
  | .Ok a => .Ok (f a)
  | .Err e => .Err (NCX_Carrier.error e)
def op33 (b : Slice U8) := do
  let r ← NCX_Reference.decode_verifier_registry_v2 b
  ok (mapReturn NCX_Carrier.registry r)
def op34 (b : Slice U8) := do
  let r ← NCX_Reference.decode_verifier_registry_entry_v2 b
  ok (mapReturn NCX_Carrier.entry r)
/-- Dictionary selection; native correspondence is a distinct gate. -/
def install (base : AdapterRw.Ops) : AdapterRw.Ops :=
  {base with op33:=op33,op34:=op34}
def configure {F E : Type} (missing : DrvC_Installation.Configuration F E) :=
  {NCV_InstallationSupport.configure missing with adapter:=install (NCV_Install.install missing.adapter)}
theorem selected (base : AdapterRw.Ops) :
    (install base).op33=op33 ∧ (install base).op34=op34 := ⟨rfl,rfl⟩
theorem sdk_selected {F E : Type} (missing : DrvC_Installation.Configuration F E) :
    (DrvC_Installation.sdk (configure missing)).op33=op33 ∧
    (DrvC_Installation.sdk (configure missing)).op34=op34 := ⟨rfl,rfl⟩
theorem ncv_retained {F E : Type} (missing : DrvC_Installation.Configuration F E) :
    (configure missing).adapter.op48=NCV_Install.op48 ∧
    (configure missing).adapter.op49=NCV_Install.op49 ∧
    (configure missing).adapter.op50=NCV_Install.op50 := ⟨rfl,rfl,rfl⟩
'''
for slot,key,fun in [(33,'registry','decode_verifier_registry_v2'),(34,'entry','decode_verifier_registry_entry_v2')]:
 s+=f'''theorem op{slot}_result (b : Slice U8) : op{slot} b =
    (match NCX_Reference.{fun} b with
      | .ok r => .ok (mapReturn NCX_Carrier.{key} r)
      | .fail e => .fail e
      | .div => .div) := by
  unfold op{slot}
  cases NCX_Reference.{fun} b <;> rfl
'''
s+='\n'.join('#print axioms '+n for n in ['selected','sdk_selected','ncv_retained','op33_result','op34_result'])+'\nend NCX_Install\nend\n';(L/'NCX_Install.lean').write_text(s)
s=s.replace('import NCV_InstallationSupport','import NCV_Install')
a=s.index('def configure');b=s.index('theorem selected',a);configuration=s[a:b];s=s[:a]+s[b:]
a=s.index('theorem sdk_selected');b=s.index('theorem op33_result',a);config_theorems=s[a:b];s=s[:a]+s[b:]
s=s.replace('#print axioms sdk_selected\n','').replace('#print axioms ncv_retained\n','').replace('open Aeneas Aeneas.Std Result AspisR1','open Aeneas Aeneas.Std Result')
(L/'NCX_Install.lean').write_text(s)
(L/'NCX_Configuration.lean').write_text('import NCX_Install\nimport NCV_InstallationSupport\nset_option autoImplicit false\nnoncomputable section\nnamespace NCX_Install\nopen Aeneas Aeneas.Std Result AspisR1\n'+configuration+config_theorems+'#print axioms sdk_selected\n#print axioms ncv_retained\nend NCX_Install\nend\n')
