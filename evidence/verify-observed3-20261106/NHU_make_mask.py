"""Frozen mask source cuts; exactly one iteration, no product arithmetic."""
from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';path='crates/aspis-core/src/state_only_hiding.rs'
src=subprocess.check_output(['git','show',rev+':'+path],cwd=R).decode()
def body_at(needle):
 start=src.index(needle)+len(needle);depth=1;i=start
 while depth:
  if src[i]=='{':depth+=1
  if src[i]=='}':depth-=1
  i+=1
 return src[start:i-1]
rows=[]
for n,name,bound,arg in [(0,'c1',16,'STATE_ONLY_HIDING_C1_COLUMNS'),(1,'mask_only_c1',10,'STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS')]:
 body=body_at('for column in 0..'+arg+' {')
 out=f'fn NHU_coeff{n}_cut({name}:&[QM31;{bound}],coefficients:&mut [QM31;27],column:usize)->usize{{let mut iter=column..{bound};if let Some(column)=iter.next(){{'+body+'\n}iter.start}\n'
 (E/f'NHU_coeff{n}_body.rs.txt').write_text(out);rows.append(dict(stage='coeff'+str(n),sha256=hashlib.sha256(body.encode()).hexdigest(),replacements=[]))
body=body_at('for exponent in (0..STATE_ONLY_HIDING_FACTOR_DEGREE).rev() {');old='prepared_linear.mul(shared)';new='prepared_cut(prepared_linear,shared,log)';assert body.count(old)==1;changed=body.replace(old,new);assert changed.replace(new,old)==body
out='fn NHU_horner_cut(coefficients:&[QM31;27],prepared_linear:PreparedQm31Multiplier,mut shared:QM31,n:usize,log:&mut PreparedLog)->(QM31,usize){let mut iter=(0..n).rev();if let Some(exponent)=iter.next(){'+changed+'\n}(shared,iter.len())}\n'
(E/'NHU_horner_body.rs.txt').write_text(out);rows.append(dict(stage='horner',sha256=hashlib.sha256(body.encode()).hexdigest(),replacements=[[old,new]]))
body=src[src.index('    shared.add(\n        QM31::ONE\n            .add(mask_power_26(explicit_linear))'):].split('\n}',1)[0]
old='''QM31::ONE
            .add(mask_power_26(explicit_linear))
            .mul(explicit_g)'''
new='multiply_tail(QM31::ONE.add(power_tail(explicit_linear,log)),explicit_g,log)';assert body.count(old)==1;changed=body.replace(old,new);assert changed.replace(new,old)==body
(E/'NHU_mask_tail_body.rs.txt').write_text('fn NHU_mask_tail_cut(shared:QM31,explicit_linear:QM31,explicit_g:QM31,log:&mut TailLog)->QM31{\n'+changed+'\n}\n');rows.append(dict(stage='tail',sha256=hashlib.sha256(body.encode()).hexdigest(),replacements=[[old,new]]))
(E/'NHU_MASK_ERASURE.json').write_text(json.dumps(dict(status='PASS',revision=rev,source_path=path,source_sha256=hashlib.sha256(src.encode()).hexdigest(),cuts=rows),indent=1)+'\n')
start=src.index('pub fn state_only_selected_mask_value(');openidx=src.index('{',start)+1
end=openidx;depth=1
while depth:
 if src[end]=='{':depth+=1
 if src[end]=='}':depth-=1
 end+=1
root=src[openidx:end-1]
opening=root[:root.index('    for column in 0..STATE_ONLY_HIDING_C1_COLUMNS {')]
old='selected_mask_linears(point)';new='linears_cut(point,log)';assert opening.count(old)==1;changed=opening.replace(old,new);assert changed.replace(new,old)==opening
(E/'NHU_mask_opening_body.rs.txt').write_text('fn NHU_mask_opening_cut(point:&[QM31;10],log:&mut LinearsLog)->(QM31,QM31,[QM31;27]){'+changed+'\n(linear,explicit_linear,coefficients)\n}\n')
setup=root[root.index('    let prepared_linear ='):root.index('    for exponent in (0..STATE_ONLY_HIDING_FACTOR_DEGREE).rev() {')]
(E/'NHU_mask_setup_body.rs.txt').write_text('fn NHU_mask_setup_cut(coefficients:&[QM31;27],linear:QM31)->(PreparedQm31Multiplier,QM31){\n'+setup+'\n(prepared_linear,shared)\n}\n')
p=E/'NHU_MASK_ERASURE.json';d=json.loads(p.read_text());d.update(root_body_sha256=hashlib.sha256(root.encode()).hexdigest(),opening_sha256=hashlib.sha256(opening.encode()).hexdigest(),opening_erased_sha256=hashlib.sha256(changed.replace(new,old).encode()).hexdigest(),setup_sha256=hashlib.sha256(setup.encode()).hexdigest(),root_sequence=['opening','coeff0 loop(16)','coeff1 loop(10)','setup','horner loop(26)','tail']);p.write_text(json.dumps(d,indent=1)+'\n')
