from pathlib import Path
import subprocess,json,hashlib,difflib,re
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';source='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';old=subprocess.check_output(['git','show',rev+':'+source],text=True);code=(E/'NKR_TermHorner_native.rs.txt').read_text()
def body(s,name):
 p=s.index('fn '+name+'(');p=s.index('{',p);q=p+1;d=1
 while d:d+=(s[q]=='{')-(s[q]=='}');q+=1
 return s[p+1:q-1]
compact=lambda s:re.sub(r'\s+','',s)
b=body(old,'composition_parts');start=b.index('    let prepared_theta =');end=b.index('    Ok((',start);frozen=b[start:end]
expected='''let prepared_theta = PreparedQm31Multiplier::new(theta);let mut composition = copy.residual;
for lane in semantic.into_iter().rev() {composition = prepared_theta.mul(composition).add(lane);}
for lane in poseidon.into_iter().rev() {composition = prepared_theta.mul(composition).add(lane);}'''
assert compact(frozen)==compact(expected),'Frozen Horner control changed'
assert compact(body(code,'NKR_horner_step'))=='NKR_horner_add(NKR_horner_mul(prepared_theta,composition,l),lane,l)'
translated='''let prepared_theta=NKR_horner_new(theta,l);
for lane in semantic.into_iter().rev(){NKR_horner_visit(prepared_theta,lane,l);}
for lane in poseidon.into_iter().rev(){NKR_horner_visit(prepared_theta,lane,l);}'''
assert compact(body(code,'NKR_horner_control'))==compact(translated)
name='crates/aspis-statement/src/pool_v1/NKR_TermHorner_native.rs';new=old+'\n#[cfg(kani)]\n#[path="NKR_TermHorner_native.rs"]\nmod NKR_horner_native;\n';patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source));patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name));(E/'NKR_TermHorner_native.patch').write_text(patch)
(E/'NKR_TermHorner_TRANSCRIPTION.json').write_text(json.dumps(dict(revision=rev,source=source,source_sha256=hashlib.sha256(old.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest(),frozen=frozen,translated_control=translated,identity=True,shape=['NKR_horner_step_cut','NKR_horner_control_cut'],scope='One nativeiteration on arbitrarycache/state/lane/replies; dataindependent24+4reversecontrol+theta/cachesamecall (ad). Control IDlabels carry no fieldvaluecredit.'),indent=2))
print('237Horner native step/control frozen windows PASS')
