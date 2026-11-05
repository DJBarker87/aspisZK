from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
proofs=[]
for file,path,mod,functions in [
 ('NHU_hiding.rs.txt','crates/aspis-core/src/state_only_hiding.rs','NHU_native',[
 ('cm31_mul_i','i','value.a.0<crate::field::P && value.b.0<crate::field::P','NHU_native::NHU_ref_i(value)'),
 ('cm31_mul_r','r','value.a.0<crate::field::P && value.b.0<crate::field::P','NHU_native::NHU_ref_r(value)'),
 ('mul_tower_basis','tower','coordinate<4 && value.c0.a.0<crate::field::P && value.c0.b.0<crate::field::P && value.c1.a.0<crate::field::P && value.c1.b.0<crate::field::P','NHU_native::NHU_ref_tower(value,coordinate)')]),
 ('NHU_statement_source.rs.txt','crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs','NHU_native',[
 ('lift_m31','lift',None,'NHU_native::NHU_ref_lift(value)')])]:
 original=subprocess.check_output(['git','show',rev+':'+path],cwd=R).decode();changed=original;insertions=[]
 for fun,tag,domain,reference in functions:
  attrs=(f'#[cfg_attr(kani, kani::requires({domain}))]\n' if domain else '')+f'#[cfg_attr(all(kani,not(NHU_bad_{tag})), kani::ensures(|result| *result=={reference}))]\n#[cfg_attr(all(kani,NHU_bad_{tag}), kani::ensures(|result| *result!={reference}))]\n#[cfg_attr(kani, kani::modifies())]\n'
  needle='fn '+fun+'(';assert changed.count(needle)==1;changed=changed.replace(needle,attrs+needle);insertions.append(attrs)
  proofs.append(dict(function=path+'::'+fun,domain=domain or 'all raw inputs',reference=reference,modifies=[],control='NHU_bad_'+tag,body_unchanged=True))
 erased=changed
 for attrs in insertions:assert erased.count(attrs)==1;erased=erased.replace(attrs,'')
 assert erased==original
 suffix='\n#[cfg(kani)]\nmod NHU_native { include!("NHU_native.rs"); }\n' if path.startswith('crates/aspis-core/') else '\n#[cfg(kani)] mod NHU_native { include!("NHU_statement.rs"); }\n'
 (E/file).write_text(changed+suffix)
p=E/'NHU_core.rs.txt';s=p.read_text();needle='include!("NHU_contracts.rs");'
if needle not in s:p.write_text(s+'\n'+needle+'\n')
o=json.loads((E/'NHU_OVERLAY.json').read_text());o['crates/aspis-core/src/NHU_contracts.rs']='NHU_contracts.rs.txt';(E/'NHU_OVERLAY.json').write_text(json.dumps(o,indent=1)+'\n');(E/'NHU_SOURCE_PINS.json').write_text(json.dumps({p:hashlib.sha256((E/s).read_bytes()).hexdigest() for p,s in o.items()},indent=1)+'\n');(E/'NHU_CONTRACT_ERASURE.json').write_text(json.dumps(dict(status='PASS',revision=rev,functions=proofs,reference_extraction='Reuse already-emitted probe/constructor definitions and NHU_MaskHelpers natural word laws; no fresh reference extraction',native_body_checks='Earlier ordinary body checks retained as support; full proof_for_contract checks are required for small immutable helpers'),indent=1)+'\n')
