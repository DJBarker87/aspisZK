from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent
s=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-statement/src/state_only_poseidon.rs'],text=True)
h=(E/'NKG_state_native.rs').read_text()
def body(s,at):
 i=s.index('{',at);j=i+1;d=1
 while d:d+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[i+1:j-1]
def tokens(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[^\s]',re.sub(r'//[^\n]*','',s))
b=body(s,s.index('while lane < POSEIDON2_WIDTH',s.index('fn interpolate_three_constant_columns(')))
expected=b.replace('interpolate_three_constant_limb(','NKG_limb(log,').replace('lane += 1;','*lane += 1;').replace('[lane]','[*lane]')
actual=body(h,h.index('if *lane<POSEIDON2_WIDTH'))
assert tokens(expected)==tokens(actual),'source-iteration erasure mismatch'
assert tokens(expected)!=tokens(actual.replace('column0[*lane]','column1[*lane]',1))
ib=body(s,s.index('fn interpolated_internal_pair('))
ie=ib.replace('qm31_m31_dot(', 'NKG_dot(log,').replace('internal_round(', 'NKG_round(log,')
ie=ie.replace('NKG_round(log,NKG_round(log,state, even), odd)', 'let middle = NKG_round(log,state, even);\n    NKG_round(log,middle, odd)')
ia=body(h,h.index('fn NKG_internal_pair('));assert tokens(ie)==tokens(ia)
assert tokens(ie)!=tokens(ia.replace('2 * (row - 2) + 1','2 * (row - 2)',1))
fb=body(s,s.index('fn interpolated_full_pair_packed('))
fe=fb.replace('interpolate_three_constant_columns(', 'NKG_columns(log,').replace('full_round_packed(full_round(state, even), odd)','{let middle=NKG_full(log,state,even);NKG_full_packed(log,middle,odd)}')
fa=body(h,h.index('fn NKG_full_pair('));assert tokens(fe)==tokens(fa)
assert tokens(fe)!=tokens(fa.replace('EXTERNAL_INITIAL[2]','EXTERNAL_INITIAL[3]',1))
root=body(s,s.index('pub fn evaluate_state_only_poseidon_oracle_projected('))
low=root[:root.index('    let leading =')]
low=low.replace('sum.add(selectors.local[row])','NKG_control_add(log,row)').replace('|sum, row|','|_sum,row|')
control=body(h,h.index('fn NKG_low_controller('));control=control[:control.index('let _=')]
assert tokens(low)==tokens(control),'fold control source erasure'
start=root.index('    let leading =');end=root.index('    let prepared_weights =')
prefix=root[start:end].replace('openings','o').replace('selectors','s').replace('leading_pair_packed(', 'NKG_lead(log,').replace('interpolated_full_pair_packed(', 'NKG_full_child(log,').replace('interpolated_internal_pair(', 'NKG_internal_child(log,')
assert tokens(prefix+'(leading,full,internal)')==tokens(body(h,h.index('fn NKG_prefix(')))
group=body(root,root.index('core::array::from_fn(|group|'))
pack=group[:group.index('//')].replace('qm31_pack_base4(', 'NKG_pack(log,').replace('openings.succ_z','succ')
tail=group[group.index('prepared_block.mul'):]
original_tail='prepared_block.mul(qm31_sum_products3_prepared(&prepared_weights,&[target.sub(leading[group]),target.sub(full[group]),target.sub(internal),],))'
assert tokens(tail)==tokens(original_tail),'unexpected projected arithmetic body'
expanded=pack+'let d0=NKG_sub(log,target,leading[group]);let d1=NKG_sub(log,target,full[group]);let d2=NKG_sub(log,target,internal);let sum=NKG_sum(log,prepared_weights,&[d0,d1,d2]);NKG_pmul(log,prepared_block,sum)'
assert tokens(expanded)==tokens(body(h,h.index('fn NKG_group(')))
pack_segment=body(h,h.index('fn NKG_pack_segment('));pack_segment=pack_segment[:pack_segment.rindex('(target,internal)')]
sub_segment=body(h,h.index('fn NKG_sub_segment('));sub_segment=sub_segment[:sub_segment.rindex('[d0,d1,d2]')]
sum_segment=body(h,h.index('fn NKG_sum_segment(')).replace('log,p,differences','log,prepared_weights,&[d0,d1,d2]')
mul_segment=body(h,h.index('fn NKG_mul_segment(')).replace('log,p,sum','log,prepared_block,sum')
assert tokens(pack_segment+sub_segment+'let sum='+sum_segment+';'+mul_segment)==tokens(expanded),'split chain is not exact source group'
assert tokens(expanded)!=tokens(expanded.replace('leading[group]','full[group]',1))
rows=json.loads((E/'NKG_BASELINE_ROWS.json').read_text());frozen_bytes=s.encode()
for row in rows:
 cert=row['obligation']['certificate'];lo,hi=cert['frozen_body_byte_range'];assert hashlib.sha256(frozen_bytes[lo:hi]).hexdigest()==row['frozen_body_sha256'],row['row']
x=dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_sha256=hashlib.sha256(s.encode()).hexdigest(),harness_sha256=hashlib.sha256(h.encode()).hexdigest(),column_iteration_exact_token_erasure=True,internal_pair_exact_token_erasure=True,full_pair_exact_token_erasure=True,projected_control_exact=True,projected_prefix_exact=True,projected_group_and_four_segments_exact=True,baseline_body_hashes_verified=[r["row"] for r in rows],argument_mutations_rejected=4)
(E/'NKG_SOURCE_ASSOCIATION.json').write_text(json.dumps(x,indent=2)+'\n');print('NKG source association PASS: four frozen body hashes and all native source segments; mutations rejected')
