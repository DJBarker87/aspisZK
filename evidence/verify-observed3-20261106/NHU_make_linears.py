from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1]
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-core/src/state_only_hiding.rs'
src=subprocess.check_output(['git','show',rev+':'+path],cwd=R).decode()
def body_at(needle):
 start=src.index(needle)+len(needle);depth=1;i=start
 while depth:
  if src[i]=='{':depth+=1
  if src[i]=='}':depth-=1
  i+=1
 return src[start:i-1]
body=body_at('for variable in (0..STATE_ONLY_HIDING_SUMCHECK_ROUNDS).rev() {')
cut='fn NHU_linear_step(point:&[QM31;10],mut suffix:QM31,mut weighted:QM31,n:usize)->(QM31,QM31,usize){\nlet mut iter=(0..n).rev();\nif let Some(variable)=iter.next(){'+body+'\n}\n(suffix,weighted,iter.len())\n}\n'
(E/'NHU_linear_body.rs.txt').write_text(cut)
(E/'NHU_LINEAR_ERASURE.json').write_text(json.dumps(dict(status='PASS',revision=rev,source_path=path,source_sha256=hashlib.sha256(src.encode()).hexdigest(),selected_loop_body_sha256=hashlib.sha256(body.encode()).hexdigest(),generated_body_sha256=hashlib.sha256(cut.encode()).hexdigest(),method='Exact loop body, unchanged; arbitrary reverse Range prestate n<=10; one real iterator next; original field adds execute'),indent=1)+'\n')

full=body_at('fn selected_mask_linears(point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]) -> (QM31, QM31) {')
tail=full[full.index('\n    (\n'):]
replacements=[(f'{v}.mul_m31(M31({k}))',f'scalar_cut({v},M31({k}),log)') for v,k in [('suffix',3),('weighted',22),('suffix',275),('weighted',150)]]
changed=tail
for old,new in replacements:assert changed.count(old)==1;changed=changed.replace(old,new)
erased=changed
for old,new in reversed(replacements):erased=erased.replace(new,old)
assert erased==tail
(E/'NHU_linear_suffix_body.rs.txt').write_text('fn NHU_linear_suffix(suffix:QM31,weighted:QM31,log:&mut ScalarLog)->(QM31,QM31){'+changed+'\n}\n')
p=E/'NHU_LINEAR_ERASURE.json';d=json.loads(p.read_text());d.update(suffix_original_sha256=hashlib.sha256(tail.encode()).hexdigest(),suffix_erased_sha256=hashlib.sha256(erased.encode()).hexdigest(),suffix_replacements=replacements);p.write_text(json.dumps(d,indent=1)+'\n')
