"""Pin the actual guard/producer bodies; this records structural cuts, not proof credit."""
from pathlib import Path
import hashlib,json,subprocess,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028'
spec={
 'N2':{'crates/aspis-prover/src/state_only_hiding.rs':['sample_mask_h1_padding','sum_qm31_copy_inactive','inactive_qm31_step','state_only_copy_inactive_sum_qm31','state_only_copy_inactive_sum_m31','balance_qm31_copy_inactive','apply_h1_padding_mask_for_active','check_h1_padding_active','h1_padding_inactive_sum','h1_padding_inactive_step']},
 'N3':{'crates/aspis-core/src/field/ct.rs':['subtract_p','add','sub'],'crates/aspis-r1-cost-probe/src/host_semantic.rs':['check_semantic_columns','check_base_columns','check_base_column','check_secure_column']},
 'N4':{'crates/aspis-prover/src/state_only_hiding.rs':['balance_m31_copy_inactive','sum_m31_copy_inactive','inactive_m31_step','balance_mask_column'],'crates/aspis-r1-cost-probe/src/prover.rs':['audit_masks','inactive_sum_m31','inactive_sum_k','prove_masked_with_attempt']},
 'N5':{'crates/aspis-r1-cost-probe/src/prover_helper_sum.rs':['state_only_copy_helper_sum'],'crates/aspis-r1-cost-probe/src/host_semantic.rs':['build_with_helper_mode']},
 'N6':{'crates/aspis-r1-cost-probe/src/host_sumcheck.rs':['interpolate','prove_sumcheck_rounds','prove_sumcheck_round','evaluate_assignment','merge_evaluations']}}
rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip();out={}
for site,files in spec.items():
 out[site]=[]
 for path,names in files.items():
  b=(R/path).read_bytes();s=b.decode();blob=subprocess.check_output(['git','rev-parse',rev+':'+path],cwd=R,text=True).strip()
  for name in names:
   start=re.search(r'\bfn '+re.escape(name)+r'\b',s).start();opening=s.index('{',start);depth=1;i=opening+1
   while depth:
    if s[i]=='{':depth+=1
    if s[i]=='}':depth-=1
    i+=1
   body=s[start:i]
   out[site].append(dict(path=path,source_revision=rev,git_blob=blob,file_sha256=hashlib.sha256(b).hexdigest(),function=name,line=1+s[:start].count('\n'),body=body,body_sha256=hashlib.sha256(body.encode()).hexdigest()))
(E/'native-sites.json').write_text(json.dumps(out,indent=2)+'\n')
print('Pinned',sum(map(len,out.values())),'native bodies; no equivalence or honest-run claim inferred')
