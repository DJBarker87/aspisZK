from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent;R=E.parents[1];F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
src=subprocess.check_output(['git','show',F+':crates/aspis-r1-cost-probe/src/r1_semantic.rs'],cwd=R,text=True)
a=src.index('pub fn verify_observed<');start=src.index('{',a);i=start+1;depth=1
while depth:depth+=(src[i]=='{')-(src[i]=='}');i+=1
body=src[start+1:i-1]
new=body.replace('Prefix::parse(bytes)','ops.parse(bytes)').replace('public_transcript(public, hash, prefix.c1_root)','ops.public_transcript(public, hash, prefix.c1_root)').replace('wire::begin(&prefix, &mut transcript)','ops.begin(&prefix, &mut transcript)').replace('verify_finish(public, prefix, transcript, challenges, obs)','ops.finish(public, prefix, transcript, challenges, obs)').replace('    mark(obs, 0);','    ops.prefix_address=&prefix as *const _ as usize;\n    mark(obs, 0);').replace('    let challenges =','    ops.transcript_address=&transcript as *const _ as usize;\n    let challenges =')
text=(E/'NFW_semantic_control.rs.txt').read_text().replace('NFW_FROZEN_SEMANTIC_BODY',new)
p=E/'NFW_prefix_prepare.py';s=p.read_text();pos=s.index("for suffix in ['', '_renamed']:")
s=s[:pos]+"semantic+="+repr(text)+"\n"+s[pos:];s=s.replace('fn verify_error_root{suffix}(){{verify_error();}}','fn verify_error_root{suffix}(){{semantic_check();}}')
s=s.replace("semantic='''use super::*;", "semantic='''use super::*;\ninclude!(concat!(env!(\"CARGO_MANIFEST_DIR\"),\"/../../KMX_stubs.rs\"));")
s=s.replace("semantic+=f'#[kani::proof] #[kani::unwind(64)]", "semantic+=f'#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)] #[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]\\n#[kani::proof] #[kani::unwind(64)]")
# Typed constructors/getter live only in a cfg(kani) module appended to scratch.
needle="files={C+'NFW_public.rs':public,C+'NFW_prefix.rs':candidate,C+'NFW_semantic_prefix.rs':semantic}"
wire="\n#[cfg(kani)] pub(crate) mod NFW_prefix_wire { use super::*;pub(crate) fn prefix<'a>(c1_root:&'a[u8;32],records:[&'a[u8];27])->Prefix<'a>{Prefix{c1_root,records}}pub(crate) fn cursor<H:Digest32>(t:&SemanticTranscript<H>)->u8{t.next_row}}\n"
s=s.replace(needle,needle+"\nwire_extra="+repr(wire))
needle="x=json.loads((E/'NFW_NATIVE_INPUTS.json').read_text())"
s=s.replace(needle,needle+"\nfiles[C+'r1_wire.rs']=x[C+'r1_wire.rs']+wire_extra")
p.write_text(s)
(E/'NFW_SEMANTIC_CONTROL_SOURCE.json').write_text(json.dumps(dict(frozen_revision=F,original_body=body,local_record_body=new,extra_ghosts=['prefix address bound immediately after the actual parsed-prefix binding','transcript address bound immediately after the actual public-transcript binding'],scope='Complete caller failure-stage/control and selected arguments/reply projections; native typed-record semantic transport retained under P6/D188. Prefix record validity, full output carrier and byte/model lift remain OPEN; no row admission.'),indent=1)+'\n')
