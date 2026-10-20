#!/usr/bin/env python3
"""Check the compact batched helper is exactly the old Some specialization."""
from pathlib import Path
import hashlib,importlib.util,json,re
R=Path(__file__).resolve().parents[6];B=R/'docs/research/100bit-spend-path-20261013'
spec=importlib.util.spec_from_file_location('cut',B/'tools/public-serializer-extraction-kit/extract.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
p=R/'crates/aspis-r1-cost-probe/src/verifier.rs'
old,*_=m.find_item(p,'fn accumulate_with_node(');new,*_=m.find_item(p,'fn accumulate_batched_with_node(')
s=old.decode().replace('fn accumulate_with_node(', 'fn accumulate_batched_with_node(').replace('mut pending:Option<&mut BatchedWeights>', 'weights:&mut BatchedWeights')
s=s.replace('        if let Some(weights)=pending.as_deref_mut() {\n','').replace('        } else {a.weights[j]=a.weights[j].add(a.power.mul_m31(basis[j]));}\n','').replace('    if let Some(weights)=pending {weights.terms+=1;}','    weights.terms+=1;')
compact=lambda x:re.sub(r'\s+','',x)
for name,expected in [('basis_at','fn basis_at(basis:&[M31;256],index:usize)->M31 {basis[index]}'),('accumulated_weight_at','fn accumulated_weight_at(weights:&[K],index:usize)->K {weights[index]}')]:
 getter,*_=m.find_item(p,'fn '+name+'(');assert compact(getter.decode())==compact("#[inline(always)]"+expected)
canonical_new=compact(new.decode()).replace('letwidth=a.weights.len();','').replace('width','a.weights.len()').replace('basis_at(&basis,j)','basis[j]').replace('accumulated_weight_at(&a.weights,j)','a.weights[j]')
assert compact(s)==canonical_new,'batched specialization changed arithmetic or call order'
finish,*_=m.find_item(p,'pub fn finish_relation(')
fields=sorted(set(re.findall(r'\bv\.(\w+)',finish.decode())))
assert fields==['final_message','round0','round1'],fields
out=dict(old_sha256=hashlib.sha256(old).hexdigest(),batched_sha256=hashlib.sha256(new).hexdigest(),exact_some_specialization_after_transparent_read_expansion=True,normalizations=["whitespace","fixed vector width","transparent getter expansion"],finish_relation_view_read_fields=fields,scope='Mechanical source checks; universal Rust/Lean refinement is still an obligation')
(B/'evidence/stage2-continuation-20261020/pins/batched-specialization.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
