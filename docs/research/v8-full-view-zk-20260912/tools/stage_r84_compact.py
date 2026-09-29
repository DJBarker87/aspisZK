#!/usr/bin/env python3
"""Attach a measured-only compact evaluator after both source affine gates."""
import argparse,ast,hashlib,json,re,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--native',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert m['r84_bitperm']['extra_tail_swap']
for n,h in m['files'].items():assert sha(src/n)==h,n
gates={}
for world in range(2):
    f=src/f'r84-prefix-world{world}/prefix.log';s=f.read_text()
    for marker in ['R84_FULL_AFFINE_PREFLIGHT_PASS','R19_G_WITNESS_JOINT equations=626 rank=602','R17_H1_WITNESS_JOINT rank=540','Exit status: 0']:assert marker in s,marker
    gates[str(world)]=sha(f)
nm=json.loads((a.native/'r18-stage.json').read_text());assert nm['r83_native']['variant']=='packed-block'
for n,h in nm['files'].items():assert sha(a.native/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
exrel=Path('docs/research/v8-no-work-100-20260907/experiments');ex=dst/exrel;changed=[]
def edit(n,fn):
    f=ex/n;f.write_text(fn(f.read_text()));changed.append(f)
for n in ['query_arithmetic.rs','r55_opening_check.rs']:
    shutil.copy2(a.native/exrel/n,ex/n);changed.append(ex/n)
edit('r19_channel_ordinary.rs',lambda s:s+'\n'+(here/'r83_block_dot.rs').read_text()+'\n'+(here/'r84_compact.rs').read_text())
table=(ex/'r17_basis_tables.rs').read_text()
order=ast.literal_eval(re.search(r'ORDER: \[usize; 1024\] = (\[[^;]+\]);',table)[1])
inactive=ast.literal_eval(re.search(r'INACTIVE: \[bool; 1024\] = (\[[^;]+\]);',table)[1].replace('true','True').replace('false','False'))
masks=[sum(1<<g for g in range(64)if order[16*g+l]!=1023 and inactive[order[16*g+l]]) for l in range(16)]
unique=list(dict.fromkeys(masks));ids=[unique.index(x)for x in masks];rows=[];ends=[0];complement=[]
for x in unique:
    inverse=x.bit_count()>32;complement.append(inverse)
    rows.extend(g for g in range(64)if bool(x&(1<<g))!=inverse);ends.append(len(rows))
def scalar(s):
    s=s.replace('pub(super) fn terminal_scalar(','pub(super) fn terminal_scalar_t163_retained(',1)
    for name,ty,values in [('MASKS','u64',masks),('IDS','usize',ids),('ENDS','usize',ends),('ROWS','usize',rows),('COMPLEMENT','bool',complement)]:
        replacement=f'const {name}:[{ty};{len(values)}]='+str(values).replace('True','true').replace('False','false')+';'
        s,count=re.subn(r'const '+name+r':\[[^;]+;\d+\]=\[[^;]+\];',replacement,s);assert count==1,name
    s=s.replace('let mut shared=[K::ZERO;10];',f'let mut shared=[K::ZERO;{len(unique)}];').replace('for i in 0..10 {',f'for i in 0..{len(unique)} {{')
    return s
edit('r22_scalar.rs',scalar)
def check(s):
    s=s.replace('mod r17_tensor_prefix;','mod r17_tensor_prefix;\nmod r17_owned_weights;\nmod r17_weighted_groups;\nmod r19_channel_ordinary;')
    needle='        assert_eq!(chord,dense);assert_eq!(dot(&fold(chord,a),&finals),dot(&fold(dense,a),&finals));'
    assert s.count(needle)==1
    return s.replace(needle,needle+'''
        let audit=core::array::from_fn(|i|if i<10 {source_z[i]}else{k});
        let kernel=r17_weighted_groups::Kernel::new(abc,a);let mut workspace=vec![K::ZERO;531];
        let ordinary=r19_channel_ordinary::terminal_scalar(&audit,abc,a,beta,&finals,&mut workspace,&kernel);
        let sparse=r19_channel_ordinary::r81_sparse_scalar_after_ordinary(&coins,&workspace,&kernel);
        let mut image=vec![K::ZERO;1024];image[1023]=image1;image[1022]=image2.mul(abc[1]);image[1021]=image2.mul(abc[2]).neg();
        let value=ordinary.add(beta.mul(k).mul(sparse)).add(dot(&fold(image,a),&finals));
        let r=r17_opening_weights::quotient_weights(&source_z,k,abc,tau,false);
        let g=r17_opening_weights::quotient_weights(&source_z,k,abc,tau,true);
        let dense=(0..1024).map(|i|r.weight_at(i).add(beta.mul(g.weight_at(i).sub(r.weight_at(i))))).collect();
        assert_eq!(value,dot(&fold(dense,a),&finals),"new compact full functional including image/finals case {case}");
''').replace('compact_sbf_implemented=false','compact_source_implemented=true')
edit('r84_bitperm_check.rs',check)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m.update(basis_profile='signed-bit-permutation-two-swaps',compact_primary=True,current_T_unchanged=False)
m['r84_bitperm']['host_only_preflight']=False
m['r84_compact']={'input_manifest_sha256':sha(src/'r18-stage.json'),'affine_gate_logs':gates,
    'native_manifest_sha256':sha(a.native/'r18-stage.json'),'unique_inactive_masks':len(unique),
    'inactive_sum_terms':len(rows),'new_profile':True,'security_promoted':False,'source_theorem':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'inactive_masks':len(unique),'inactive_terms':len(rows)}))
