"""Source-callee composition only; no native leaf adequacy or success premise."""
from pathlib import Path
import json,hashlib,sys
E=Path('evidence/pv-evh5-20261029');records={n:json.loads((E/(n+'-generation.json')).read_text()) for n in ['ProveSemantics','DurableWithAttempt','DurableReserveBuild']}
out='''import PV_EVH_NonceProver
import PV_EVH_MaterialFromEntropy
import PV_EVH_ApplyMaterial
import PV_EVH_BuildSemantics
import PV_EVH_ProveSemantics
import PV_EVH_PrivateSalts
set_option autoImplicit false
noncomputable section
namespace PV_EVH_LeafInstall
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (FinishedView)
variable [ExternalTypes] [ExternalFuns]
/- Local source Result transport only. Every remaining source/runtime leaf,
formatting path, native observation link and actual success is still OPEN. -/
'''
salts='prover.derive_private_salts'
configs=[('Semantics','ProveSemantics','PV_EVH_ProveSemantics',{salts:('PV_EVH_PrivateSalts','saltCallees')}),('With','DurableWithAttempt','PV_EVH_NonceWithAttempt',{'aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1':('PV_EVH_ApplyMaterial','applyCallees'),'host_semantic.build_with_material':('PV_EVH_BuildSemantics','buildCallees'),salts:('PV_EVH_PrivateSalts','saltCallees'),'prover.prove_from_semantics':('semanticInstalled','semanticCallees')}),('Reserve','DurableReserveBuild','PV_EVH_NonceReserveBuild',{'aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref':('PV_EVH_MaterialFromEntropy','materialCallees')})]
for short,rec,parent,selected in configs:
 allc=records[rec]['open_callees'];other={k:v for k,v in allc.items() if k not in selected};assert set(selected)<=set(allc)
 out+='\nstructure '+short+'Callees where\n'
 for k,v in other.items():out+='  '+v['field']+' : '+('∀ '+v['header']+', ' if v['header'] else '')+'PV_EVH_Prefix.P ('+v['result']+')\n'
 out+='\nstructure '+short+'Compatible (c : '+short+'Callees) : Prop where\n'
 for k,v in other.items():
  args=' '.join(v['args']);out+='  '+v['field'].replace('_OPEN','_fixed')+' : '+('∀ '+v['header']+', ' if v['header'] else '')+'FinishedView (c.'+v['field']+(' '+args if args else '')+') ('+k+(' '+' '.join(v['args'][1:] if k=='hash' else v['args']) if args else '')+')\n'
 # Reuse one salts interpreter both directly and in the semantic-prover spine.
 children={var:(mod+'.Callees' if mod!='semanticInstalled' else 'SemanticsCallees') for mod,var in selected.values()}
 if short=='With':children['saltCallees']='PV_EVH_PrivateSalts.Callees'
 params=''.join(' ('+var+' : '+typ+')' for var,typ in children.items())
 views=''.join(' (h_'+var+' : '+('SemanticsCompatible' if typ=='SemanticsCallees' else typ.removesuffix('.Callees')+'.Compatible')+' '+var+')' for var,typ in children.items())
 out+='\ndef install'+short+' (c : '+short+'Callees)'+params+' : '+parent+'.Callees where\n'
 def call(k,v,proof=False):
  mod,var=selected[k];args=' '.join(v['args'])
  if mod=='semanticInstalled':
   inst='(installSemantics semanticCallees saltCallees)'
   hc='(installSemantics_fixed semanticCallees saltCallees h_semanticCallees h_saltCallees)'
   return 'PV_EVH_ProveSemantics.run'+('_fixed' if proof else '')+' '+args+' '+inst+(' '+hc if proof else '')
  return mod+'.run'+('_fixed' if proof else '')+' '+args+' '+var+(' h_'+var if proof else '')
 for k,v in allc.items():
  out+='  '+v['field']+' := '+('c.'+v['field'] if k in other else ('fun '+' '.join(v['args'])+' => '+call(k,v)))+'\n'
 out+='\ntheorem install'+short+'_fixed (c : '+short+'Callees)'+params+' (hc : '+short+'Compatible c)'+views+' :\n    '+parent+'.Compatible (install'+short+' c '+' '.join(children)+') where\n'
 for k,v in allc.items():
  field=v['field'].replace('_OPEN','_fixed')
  out+='  '+field+' := '+('hc.'+field if k in other else ('fun '+' '.join(v['args'])+' => '+call(k,v,True)))+'\n'
 out+='\n#print axioms install'+short+'_fixed\n'
out+='end PV_EVH_LeafInstall\n'
p=Path('lean/PV_EVH_LeafInstall.lean');r=E/'leaf-install-generation.json'
record=json.dumps(dict(inputs={n:hashlib.sha256((E/(n+'-generation.json')).read_bytes()).hexdigest() for n in records},output_sha256=hashlib.sha256(out.encode()).hexdigest(),scope='source composition only; native adequacy, full projections and nonemptiness OPEN'),indent=2)+'\n'
if '--check' in sys.argv:assert p.read_text()==out and r.read_text()==record;print('PASS leaf installation generation')
else:p.write_text(out);r.write_text(record)
