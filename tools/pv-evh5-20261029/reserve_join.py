"""Install the proved reserve source spine, without assuming its whole Result law."""
from pathlib import Path
import hashlib,json,sys
E=Path('evidence/pv-evh5-20261029')
x=json.load(open(E/'MaskedWithAttempt-generation.json'))
source='aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1'
selected=x['open_callees'][source]['field']
other={k:v for k,v in x['open_callees'].items() if k!=source}
out='''import PV_EVH_MaskedWithAttempt
import PV_EVH_ReserveBuild
set_option autoImplicit false
noncomputable section
namespace PV_EVH_ReserveJoin
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]

/-- The eighteen remaining with-attempt callees. ReserveBuild itself has been
expanded; this does not assert that its eleven own callees are implemented. -/
structure Callees where
'''
for k,v in other.items():out+='  '+v['field']+' : '+('∀ '+v['header']+', ' if v['header'] else '')+'P ('+v['result']+')\n'
out+='\nstructure Compatible (c : Callees) : Prop where\n'
for k,v in other.items():
 app=' '.join(v['args'])
 out+='  '+v['field'].replace('_OPEN','_fixed')+' : '+('∀ '+v['header']+', ' if v['header'] else '')+'FinishedView (c.'+v['field']+(' '+app if app else '')+') ('+k+(' '+app if app else '')+')\n'
out+='\ndef install (c : Callees) (r : PV_EVH_ReserveBuild.Callees) : PV_EVH_MaskedWithAttempt.Callees where\n'
for k,v in other.items():out+='  '+v['field']+' := c.'+v['field']+'\n'
out+='  '+selected+''' := fun inst self hash binding context store =>
    PV_EVH_ReserveBuild.run inst self hash binding context store r

theorem install_fixed (c : Callees) (r : PV_EVH_ReserveBuild.Callees)
    (hc : Compatible c) (hr : PV_EVH_ReserveBuild.Compatible r) :
    PV_EVH_MaskedWithAttempt.Compatible (install c r) where
'''
for k,v in other.items():
 f=v['field'].replace('_OPEN','_fixed');out+='  '+f+' := hc.'+f+'\n'
out+='  '+selected.replace('_OPEN','_fixed')+''' := fun inst self hash binding context store =>
    PV_EVH_ReserveBuild.run_fixed inst self hash binding context store r hr

#print axioms install_fixed
end PV_EVH_ReserveJoin
'''
p=Path('lean/PV_EVH_ReserveJoin.lean');receipt=E/'reserve-join-generation.json'
record=json.dumps(dict(input='MaskedWithAttempt-generation.json',input_sha256=hashlib.sha256((E/'MaskedWithAttempt-generation.json').read_bytes()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),removed_whole_callee_assumption=source,scope='local erasure composition only; all remaining event callees and native adequacy OPEN'),indent=2)+'\n'
if '--check' in sys.argv:
 assert p.read_text()==out
 assert receipt.read_text()==record
 print('PASS reserve join generation byte identity')
else:p.write_text(out);receipt.write_text(record)
