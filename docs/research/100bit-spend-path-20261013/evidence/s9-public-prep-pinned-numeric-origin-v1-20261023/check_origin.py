from pathlib import Path
import hashlib,json
r=Path(__file__).resolve().parent;p=json.loads((r/'source-pins.json').read_text());sha=lambda x:hashlib.sha256(x).hexdigest()
t=(r/p['types_origin']).read_text();f=(r/p['funs_origin']).read_text();assert sha(t.encode())==p['types_origin_sha256'] and sha(f.encode())==p['funs_origin_sha256']
for opt in ['set_option maxHeartbeats 1000000\n','set_option maxRecDepth 2048\n']:
 assert t.count(opt)==1;t=t.replace(opt,'')
e=p['variant_expansion'];assert t.count(e['before'])==1 and t.count(e['dropped_import'])==1;t=t.replace(e['dropped_import'],'').replace(e['before'],e['after'])
assert t==(r/'sources/AspisR1PublicPreparation/Types.lean').read_text() and sha(t.encode())==p['types_adapted_sha256']
a=f.index('/-- [aspis_r1_public_preparation::aspis_core::field::{aspis_r1_public_preparation::aspis_core::field::CM31}::new]');b=f.index('/-- [aspis_r1_public_preparation::aspis_core::field::{aspis_r1_public_preparation::aspis_core::field::QM31}::ZERO]',a);cm=f[a:b].strip()
a=f.index('/-- [aspis_r1_public_preparation::aspis_core::field::P]');b=f.index('\n\n',f.index('@[global_simps, irreducible] def aspis_core.field.P',a));pd=f[a:b].strip()
a=f.index('/-- [aspis_r1_public_preparation::sampler::qm31_div_pass]: loop body 0:');b=f.index('/-- [aspis_r1_public_preparation::r1_wire::{aspis_r1_public_preparation::r1_wire::ValidatedRecord',a);s=f[a:b].strip();needle='Array.make 4#usize [ i1, i3, i5, i7 ]';assert s.count(needle)==1;s=s.replace(needle,needle+' (by rfl)')
header='-- Source-pinned numerical reference owner only; no parser/caller claims.\nimport Aeneas\nimport AspisR1PublicPreparation.Types\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option autoImplicit false\nnamespace AspisR1PublicPreparation\n'
want=header+'\n\n'+cm+'\n\n'+pd+'\n\n'+s+'\n\nend AspisR1PublicPreparation\n';actual=(r/'sources/AspisR1PublicPreparation/Funs.lean').read_text();assert want==actual and sha(actual.encode())==p['funs_selected_sha256']
print('PASS: known raw source pins, explicit qualified Variant expansion, resource cleanup, exact numeric selection and literal array-length proof port; no old cache identity claim')
