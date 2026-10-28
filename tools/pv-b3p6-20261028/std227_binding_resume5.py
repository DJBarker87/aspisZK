"""Fail-closed source/body-law association for ruling x-prime.
This is a source argument around the checked models, not a proof of different
compiler cohorts or of native machine execution.
"""
from pathlib import Path
import json,re,hashlib
D=Path('evidence/pv-b3p6-20261028');x=json.load(open(D/'std227-comparison-stdcone-resume5.json'));rs={r['id']:r for r in x['rows']}
tokens=lambda s:re.findall(r'\w+|::|!=|==|[^\s]',re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S))
expected='''{
 if self.len() != other.len() { return false; }
 let mut idx=0;
 while idx<self.len() { if self[idx] != other[idx] { return false; } idx+=1; }
 true
}'''
assert tokens(rs[125]['deployed']['body'])==tokens(expected)
# The loop model retains first-mismatch order and all element-call Result tags;
# its natural-number measure is len-idx. It still needs its in-bounds/index/usize
# correspondence applied at the actual array caller before closure credit.
laws={70:['PV_B3P_Std194Law227.u32_u64_result','PV_B3P_Std194Law227.u32_u64_value'],117:['PV_B3P_Std194Law227.bool_u32_result'],118:['PV_B3P_Std194Law227.u16_usize_result','PV_B3P_Std194Law227.u16_usize_value'],119:['PV_B3P_Std194Law227.u8_usize_result','PV_B3P_Std194Law227.u8_usize_value'],125:['PV_B3P_Slice194227.complete_result','PV_B3P_Slice194227.same_length','PV_B3P_Slice194227.different_length']}
for ident,law in laws.items():assert rs[ident]['status']=='different-body-law-required';rs[ident]['separate_194_body_laws']=law
x['remaining_source_law_obligations']=['Apply deployed slice loop bound/index correspondence at the actual same-length array caller; separate law model is compiled, not yet a complete source link.']
x['compiler_boundary']='D381/D386 owner compiler-cohort boundary retained; generated vtable glue and intrinsic declaration do not become proved Rust-body equivalences.'
x['deployed_credit_complete']=False
(D/'std227-binding-resume5.json').write_text(json.dumps(x,indent=2)+'\n');print('source slice tokens match; laws associated; actual caller correspondence remains open')
