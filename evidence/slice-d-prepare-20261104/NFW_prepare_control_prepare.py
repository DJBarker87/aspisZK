from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent;R=E.parents[1];F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
src=subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/candidate.rs'],cwd=R,text=True)
a=src.index('fn prepare<H: Digest32>');start=src.index('{',a);i=start+1;depth=1
while depth:depth+=(src[i]=='{')-(src[i]=='}');i+=1
body=src[start+1:i-1]
new=body.replace('aspis_core::r0::heap::filled','ops.heap').replace('compact::expand_semantic','ops.expand_semantic').replace('compact::expand_values','ops.expand_values').replace('wide_view(proof,','ops.wide_view(proof,').replace('crate::r1_semantic::verify_observed(public, v.semantic, hash, obs)','ops.verify(public, v.semantic, hash)').replace('    mark(obs, Phase::Semantic);','    ops.sem_address=&sem as *const _ as usize;\n    mark(obs, Phase::Semantic);').replace('Prepared::new(&sem, &v, hash, g)','ops.prepared(&sem, &v, hash, g)')
text=(E/'NFW_prepare_control.rs.txt').read_text().replace('NFW_FROZEN_PREPARE_BODY',new)
# Hook only this unlaunched parent's family. No verdict obtained under the old name.
p=E/'NFW_prefix_prepare.py';s=p.read_text();pos=s.index('for name,stub in')
s=s[:pos]+"candidate+= "+repr(text)+"\n"+s[pos:]
s=s.replace("candidate+=f'#[kani::proof] #[kani::unwind(64)] {stub}","candidate+=f'#[kani::proof] #[kani::unwind(258)] {stub}")
s=s.replace("fn {name}_root{suffix}(){{{name}();}}", "fn {name}_root{suffix}(){{{\"spine_check\" if name==\"prepare_error\" else name}();}}")
# Exact KMX patch functions only; both native copies are covered by the same family.
s=s.replace("candidate+=f'#[kani::proof]", "candidate+=f'#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)] #[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]\\n#[kani::proof]")
s=s.replace("candidate='''use super::*;", "candidate='''use super::*;\ninclude!(concat!(env!(\"CARGO_MANIFEST_DIR\"),\"/../../KMX_stubs.rs\"));")
p.write_text(s)
(E/'NFW_PREPARE_CONTROL_SOURCE.json').write_text(json.dumps(dict(frozen_revision=F,original_body=body,local_record_body=new,extra_ghost='Only sem_address bound AFTER the actual returned-sem binding, then checked at Prepared child entry.',domain='S2 fixed proof length57607, arbitrary original proof bytes, zero initial caller g, deployed None observer, arbitrary seven local callee failure/success paths and full typed sem/Prepared/g replies. Child data semantics and original bytes-to-model lift remain OPEN; no row admission.'),indent=1)+'\n')
