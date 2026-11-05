from pathlib import Path
import json,hashlib,re,subprocess,runpy
E=Path(__file__).resolve().parent;x=runpy.run_path(str(E/'NHE_native_prepare.py'));inputs=x['inputs'];code=inputs['crates/aspis-r1-cost-probe/src/NHE_scalar.rs']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
frozen=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-r1-cost-probe/src/weights.rs'],text=True)
def body(s,n):
 a=s.index('fn '+n+'(');b=s.index('{',a);depth=1;c=b+1
 while depth:depth+=(s[c]=='{')-(s[c]=='}');c+=1
 return s[a:c]
norm=lambda s:re.sub(r'\s+','',s)
actual=body(frozen,'scalar_factor');compiled=body(inputs['crates/aspis-r1-cost-probe/src/weights.rs'],'scalar_factor')
assert norm(actual)==norm(compiled)
step=body(code,'source_step').split('{',1)[1][:-1]
erased=norm(step.replace('product(p[PERM[s]],f[s],l)','p[PERM[s]].mul_qm31(f[s])'))
assert erased=='v.add(p[PERM[s]].mul_qm31(f[s]))'
assert '(0..4).fold(E::ZERO,|v,s|'+erased+').mul_m31(QUARTER)'in norm(actual)
final=norm(body(code,'source_final').split('{',1)[1][:-1]);assert final=='quarter(v,QUARTER,l)'
assert not re.search(r'\bstatic\b|Option\s*<\s*fn\b',code)
kmx=sha(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch')
rows=[]
for g in range(50):
 a=f'NHE_K{2*g+1:03d}';b=f'NHE_K{2*g+2:03d}'
 p=json.loads((E/a/'receipt.json').read_text());n=json.loads((E/b/'receipt.json').read_text());assert p['module']==n['module']==f'weights::NHE_scalar::g{g:02d}'
 assert p['exit_status']==0 and n['exit_status']==1 and p['source_hashes']==n['source_hashes']
 assert 'VERIFICATION:- SUCCESSFUL'in(E/a/'stdout.log').read_text()
 assert 'Failed Checks: assertion failed: good'in(E/b/'stdout.log').read_text()
 for name in [a,b]:
  graph=json.loads((E/(name+'-graph-check.json')).read_text());lock=json.loads((E/(name+'-lock-check.json')).read_text());assert graph['graph_matches_frozen']and lock['unchanged']
 rows.append(dict(group=g,positive=a,negative=b,module=p['module'],property=json.loads((E/'NHE_SCALAR_PLAN.json').read_text())['group_ranges']))
result=dict(status='PASS LOCAL OBSERVATIONS ONLY',native_pairs=50,rows=rows,kmx_patch_sha256=kmx,source_erasure=True,native_product_evaluated=False,paired_product='NHE_ScalarProductLaw.product L071',paired_quarter='AspisR1.NGM_RoundScale.total',reference='NGW_HelperRef.polynomial_step_ref; NHE_ScalarCell.total L076',quarantined_option_fn=[],suspended_writable_static=[],composed_status='OPEN',blocker='L077 default-recursion failure on emitted closure association; then four-step domain/canonical/frame induction and terminal-scale source/model composition remain',trust='P6/D188 option A retained/reclassified; no trust removal or new row')
(E/'NHE_SCALAR_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS 50 native scalar observation/control pairs; scalar_factor OPEN')
