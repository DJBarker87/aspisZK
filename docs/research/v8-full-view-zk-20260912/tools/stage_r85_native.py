#!/usr/bin/env python3
"""Exact-output private-kernel experiments against the measured R84 profile."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
p.add_argument('--variant',choices=['quotient','ordinary','compose'],required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert 'r84_compact' in m and 'r85_native' not in m
assert sha(src/'sbf-primary/aspis_v8_performance_sbf.so')=='f4256c5aea3fc28c6ccffd2ef2e3e0e4a3cf7922ba41e5b122eff9bebc876b6a'
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
def edit(n,fn):
    f=ex/n;old=f.read_text();new=fn(old);assert new!=old,n;f.write_text(new);changed.append(f)
edit('r81_canonical_basis.rs',lambda s:s+'\n'+(here/'r85_private_ops.rs').read_text())
if a.variant in ['quotient','compose']:
    edit('quotient_fold.rs',lambda s:s+'\n'+(here/'r85_quotient.rs').read_text())
    def opened(s):
        start=s.index('pub(super) fn opened_channel(');end=s.index('// New-profile verifier suffix.',start)
        part=s[start:end]
        needle='    let iv = crate::r19_channel_fold::interpolant(p.iv,iv_g,beta);';assert part.count(needle)==1
        part=part.replace(needle,needle+'\n    let canonical=quotient_fold::Canonical::new(alpha,iv);')
        needle='            let mut q = [K::ZERO; 4];';assert part.count(needle)==1
        part=part.replace(needle,'''            if let (Some(canonical),Ok((inverses,base_inverses)))=(&canonical,&inverse_batch) {
                let inv:[K;4]=inverses[4*i..4*i+4].try_into().unwrap();
                if let Some(folded)=canonical.divided(all,inv,if p.use_x{base.x}else{base.y},
                    p.use_x,base_inverses[2*i],base_inverses[2*i+1]) {
                    values[channel].push(folded);continue;
                }
            }
'''+needle)
        return s[:start]+part+s[end:]
    edit('r17_host_relation.rs',opened)
    def check(s):
        if 'mod quotient_fold;' not in s:s=s.replace('mod query_arithmetic;','mod query_arithmetic;\nmod quotient_fold;')
        needle='query_arithmetic::r55_controls();';assert s.count(needle)==1
        return s.replace(needle,needle+'quotient_fold::r85_controls();')
    edit('r55_opening_check.rs',check)
if a.variant in ['ordinary','compose']:
    source=(here/'r84_compact.rs').read_text()
    begin=source.index('    let z=');end=source.index('\n#[inline(always)]')
    body=source[begin:end].replace('K::','CQ::').replace('[K;','[CQ;')
    body=body.replace('let z=core::array::from_fn(|i|audit[i]);\n    let points=corelib::v6_transcript::v6_statement_points(&z);',
        '''let source_z=core::array::from_fn(|i|audit[i]);
    let audit=r85_convert(*audit)?;let abc=r85_convert(abc)?;let alpha=r85_convert(alpha)?;
    let beta=r85_in(beta)?;let finals=r85_convert(*finals)?;
    let original_points=corelib::v6_transcript::v6_statement_points(&source_z);
    let points=[r85_convert(original_points[0])?,r85_convert(original_points[1])?];
    let mut qentries=[CQ::ZERO;4];''')
    body=body.replace('entries.fill(CQ::ZERO);','').replace('r83_block_terminal(','r85_block_terminal(')
    body=body.replace('corelib::field::qm31_sum_products2(','CQ::dot(')
    body=body.replace('&powers,finals)','&powers,&finals)').replace('entries[i]=entries[i].add(entry);','qentries[i]=qentries[i].add(entry);')
    assert body.endswith('    plain\n}')
    body=body[:-len('    plain\n}')]+'''    *entries=qentries.map(r85_out);
    Some(r85_out(plain))
}'''
    block=(here/'r83_block_dot.rs').read_text().replace('r83_block_terminal','r85_block_terminal').replace('K','CQ')
    block=block.replace('use corelib::field::{qm31_sum_products2 as dot2,qm31_sum_products3 as dot3,qm31_sum_products4 as dot4};',
        '''fn dot2(a:[CQ;2],b:[CQ;2])->CQ{CQ::dot(a,b)}
    fn dot3(a:[CQ;3],b:[CQ;3])->CQ{CQ::dot(a,b)}
    fn dot4(a:[CQ;4],b:[CQ;4])->CQ{CQ::dot(a,b)}''')
    addition='''
#[path="r81_canonical_basis.rs"] mod r85_private;
use r85_private::Q as CQ;
use corelib::field::M31;
fn r85_in(v:K)->Option<CQ>{CQ::from_limbs([v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0])}
fn r85_out(v:CQ)->K{let [a,b,c,d]=v.limbs();K{c0:corelib::field::CM31::new(M31(a),M31(b)),c1:corelib::field::CM31::new(M31(c),M31(d))}}
fn r85_convert<const N:usize>(v:[K;N])->Option<[CQ;N]>{let mut out=[CQ::ZERO;N];for i in 0..N{out[i]=r85_in(v[i])?;}Some(out)}
#[inline(never)]
fn r85_prepare(audit:&[K;11],abc:[K;3],alpha:[K;4],beta:K,finals:&[K;4],entries:&mut[K;4])->Option<K>{
'''+body+'\n'+block+'''
fn r84_prepare(audit:&[K;11],abc:[K;3],alpha:[K;4],beta:K,finals:&[K;4],entries:&mut[K;4])->K{
    r85_prepare(audit,abc,alpha,beta,finals,entries)
        .unwrap_or_else(||r84_prepare_retained(audit,abc,alpha,beta,finals,entries))
}
#[cfg(not(target_os="solana"))]
pub(super) fn r85_prepare_check(audit:&[K;11],abc:[K;3],alpha:[K;4],beta:K,finals:&[K;4]) {
    let mut a=[K::ZERO;4];let mut b=[K::ONE;4];
    let expected=r84_prepare_retained(audit,abc,alpha,beta,finals,&mut a);
    assert_eq!(r85_prepare(audit,abc,alpha,beta,finals,&mut b),Some(expected));
    assert_eq!(a,b);
    let mut bad=*audit;bad[0].c0.a.0=corelib::field::P;
    assert_eq!(r85_prepare(&bad,abc,alpha,beta,finals,&mut b),None);
}
'''
    def ordinary(s):
        assert s.count('fn r84_prepare(')==1
        return s.replace('fn r84_prepare(','fn r84_prepare_retained(',1)+'\n'+addition
    edit('r19_channel_ordinary.rs',ordinary)
    needle='        let sparse=r19_channel_ordinary::r81_sparse_scalar_after_ordinary(&coins,&workspace,&kernel);'
    def ordinary_check(s):
        assert s.count(needle)==1
        return s.replace(needle,'        r19_channel_ordinary::r85_prepare_check(&audit,abc,a,beta,&finals);\n'+needle)
    edit('r84_bitperm_check.rs',ordinary_check)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r85_native']={'variant':a.variant,'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
    'protocol_changed':False,'validation_removed':False,'new_security_claim':False,'selected':False,
    'fixtures':[{'path':str(src/f'r24-host-a/fixture-world{w}'),'sha256':sha(src/f'r24-host-a/fixture-world{w}/proof-1.bin')}for w in range(2)]}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'variant':a.variant}))
