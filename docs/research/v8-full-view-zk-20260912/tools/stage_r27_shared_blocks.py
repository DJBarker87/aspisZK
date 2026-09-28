#!/usr/bin/env python3
"""Reuse tensor block products and alpha powers in the actual scalar caller."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def fn(s,needle):
    start=s.index(needle);brace=s.index('{',start);depth=0
    for i in range(brace,len(s)):
        depth+=(s[i]=='{')-(s[i]=='}')
        if depth==0:return s[start:i+1]
    raise AssertionError(needle)
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==182 and 'r27_sparse_prepare'in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists()and src.resolve()not in dst.resolve().parents;dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
path=dst/'docs/research/v8-no-work-100-20260907/experiments/r19_channel_ordinary.rs';s=path.read_text()
old=fn(s,'fn fill_tensor_support(')
new='''fn fill_tensor_support(pairs:&[[K;2];10], block1:[K;4], storage:&mut[K], blocks:&mut[K]) {
    assert_eq!(storage.len(),80);assert_eq!(blocks.len(),20);
    for r in 0..5 {for d in 0..4 {blocks[4*r+d]=if r==1 {block1[d]}else{pairs[2*r][d&1].mul(pairs[2*r+1][d>>1])};}}
    for j in 0..16 {storage[j]=blocks[j&3].mul(blocks[4+(j>>2)]);}
    let common:[K;16]=core::array::from_fn(|j|blocks[8+(j&3)].mul(blocks[12+(j>>2)]));
    for j in 0..30 {storage[16+j]=common[j&15].mul(blocks[16+(j>>4)]);}
    storage[79]=common[15].mul(blocks[19]);
}'''
s=s.replace(old,new)
old=fn(s,'fn block_terminal_scalar_impl(');new=old
new=new.replace('block1:Option<[K;4]>,finals:&[K;4]','blocks:&[K],powers:&[(K,K);4],finals:&[K;4]')
start=new.index('    let powers:');end=new.index('    let (a2, a3)',start);new=new[:start]+new[end:]
start=new.index('        let z = if round==1');end=new.index('        let (a2, a3)',start)
new=new[:start]+'        let z:&[K;4]=blocks[4*round..4*round+4].try_into().unwrap();\n'+new[end:]
start=new.index('    let z = [');end=new.index('    let stop = [',start)
new=new[:start]+'    let z:[K;4]=blocks[16..20].try_into().unwrap();\n'+new[end:]
new=new.replace('        let k = 2 * round;\n','');s=s.replace(old,new)
old=fn(s,'fn prepare_rows_scalar(');new=old
old_calls='''    fill_tensor_support(&pairs[0],blocks[0],&mut factors[..80]);
    fill_tensor_support(&pairs[1],blocks[1],&mut factors[80..160]);'''
new_calls='''    let (values,shared)=factors.split_at_mut(160);
    fill_tensor_support(&pairs[0],blocks[0],&mut values[..80],&mut shared[..20]);
    fill_tensor_support(&pairs[1],blocks[1],&mut values[80..160],&mut shared[20..40]);
    let powers:[(K,K);4]=core::array::from_fn(|i|{let square=alpha[i].mul(alpha[i]);(square,square.mul(alpha[i]))});'''
assert new.count(old_calls)==1;new=new.replace(old_calls,new_calls)
for i in range(2):new=new.replace(f'Some(blocks[{i}]),finals)',f'&shared[{20*i}..{20*i+20}],&powers,finals)')
s=s.replace(old,new)
old='    fill_tensor(&pairs,block,&mut full);fill_tensor_support(&pairs,block,&mut sparse);'
new='    fill_tensor(&pairs,block,&mut full);let mut blocks=[K::ONE;20];fill_tensor_support(&pairs,block,&mut sparse,&mut blocks);'
assert s.count(old)==1;s=s.replace(old,new);path.write_text(s);m['files'][str(path.relative_to(dst))]=sha(path)
m['r27_shared_blocks']={'control_manifest_sha256':sha(src/'r18-stage.json'),'existing_workspace_fields':[160,200],'pair_products_reused':24,'alpha_products_reused':8,'workspace_size_unchanged':531}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
