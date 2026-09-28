#!/usr/bin/env python3
"""Only compute the tensor groups read by the exact scalar T163 consumer."""
import argparse,ast,hashlib,json,re,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output;here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def function(s,needle):
    start=s.index(needle);brace=s.index('{',start);depth=0
    for i in range(brace,len(s)):
        depth+=(s[i]=='{')-(s[i]=='}')
        if depth==0:return s[start:i+1]
    raise AssertionError(needle)
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==180 and 'r25_reduction_array'in m and 'r26_schoolbook_dot'not in m
for n,h in m['files'].items():assert sha(src/n)==h,n
exrel=Path('docs/research/v8-no-work-100-20260907/experiments');support_src=src/exrel/'r18_minimal_support.rs'
support=ast.literal_eval(re.search(r'SUPPORT: \[usize;163\] = (\[.*?\]);',support_src.read_text()).group(1))
assert len(support)==len(set(support))==163 and max(support)==478 and sorted(set(i>>4 for i in support))==list(range(30))
scalar=(src/exrel/'r22_scalar.rs').read_text();assert scalar.count('entry(factors,0,SUPPORT[j])')==1 and scalar.count('entry(factors,0,1023)')==1 and scalar.count('entry(')==2
assert not dst.exists()and src.resolve()not in dst.resolve().parents;dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/exrel;ordinary=ex/'r19_channel_ordinary.rs';s=ordinary.read_text();fill=function(s,'fn fill_tensor(')
sparse=fill.replace('fn fill_tensor(','fn fill_tensor_support(',1)
old='for j in 0..64 { storage[16+j]=common[j&15].mul(blocks[4][j>>4]); }';assert sparse.count(old)==1
sparse=sparse.replace(old,'for j in 0..30 { storage[16+j]=common[j&15].mul(blocks[4][j>>4]); }\n    storage[79]=common[15].mul(blocks[4][3]);')
prepare=function(s,'fn prepare_rows_scalar(');assert prepare.count('fill_tensor(')==2
s=s.replace(prepare,prepare.replace('fill_tensor(','fill_tensor_support('))
s+='\n#[inline(never)]\n'+sparse+'\n'+'''#[cfg(not(target_os="solana"))]
pub(super) fn r27_tensor_check(x:&[K;24]) {
    let pairs=core::array::from_fn(|i|[x[2*i],x[2*i+1]]);
    let block=[x[20],x[21],x[22],x[23]];
    let mut full=[K::ZERO;80];let mut sparse=[K::ONE;80];
    fill_tensor(&pairs,block,&mut full);fill_tensor_support(&pairs,block,&mut sparse);
    for i in 0..80 {if i<46||i==79 {assert_eq!(sparse[i],full[i],"tensor coordinate {i}");}else{assert_eq!(sparse[i],K::ONE);}}
}
''';ordinary.write_text(s)
native=(here/'r21_native.rs').read_text();candidate=function(native,'pub fn compute(').replace('pub fn compute(','pub fn compute_scalar(',1)
candidate=candidate.replace('vec![K::ZERO; 1024]','vec![K::ONE; 531]').replace('r19_channel_ordinary::terminal_shared(','r19_channel_ordinary::terminal_scalar(').replace('        beta,\n        &mut workspace,','        beta,\n        &finals,\n        &mut workspace,').replace('qm31_sum_products4(ordinary, finals)','ordinary')
native+='\n#[inline(never)]\n'+candidate+'\npub fn check_tensor(x:&[K;24]) {r19_channel_ordinary::r27_tensor_check(x);}\n'
(ex/'r27_native.rs').write_text(native)
check=(here/'r22_check.rs').read_text().replace('r22_native','r27_native').replace('if case<4 {r27_native::check_adjoint(&x);}','r27_native::check_tensor(&x);').replace('R22_NATIVE source_vectors=256 adjoint_basis_cases=4096','R27_SPARSE source_vectors=256 tensor_coordinates=12032 poison_unused_coordinates=8448')
(ex/'r27_check.rs').write_text(check)
cargo=ex/'performance-host/Cargo.toml';cargo.write_text(cargo.read_text()+'\n[[bin]]\nname="r27-check"\npath="../r27_check.rs"\n')
for f in [ordinary,ex/'r27_native.rs',ex/'r27_check.rs',cargo]:m['files'][str(f.relative_to(dst))]=sha(f)
m['r27_sparse_prepare']={'control_manifest_sha256':sha(src/'r18-stage.json'),'support_sha256':sha(support_src),'groups':list(range(30))+[63],'omitted_groups':list(range(30,63)),'two_tensors':True,'ordinary_general_reference_retained':True,'new_host_sources':2}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files']),'omitted_tensor_products':66}))
