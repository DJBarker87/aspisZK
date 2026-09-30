#!/usr/bin/env python3
"""Isolate exact quotient/fold fusion on the selected unchanged R84 proofs."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--private',action='store_true');a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='b746f9549ade4d4e40ef9b0723db250a274be3e9f2b3b800f3d8b79ac89fff0d'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
def edit(name,old,new):
    f=ex/name;s=f.read_text();assert s.count(old)==1,(name,old[:90]);f.write_text(s.replace(old,new));changed.append(f)
for n in ['r99_fold_inverse.rs','r99_quotient.rs','r99_fold_check.rs']:
    f=ex/n;shutil.copy2(here/('r99_fold_inverse_private.rs' if a.private and n=='r99_fold_inverse.rs' else n),f);changed.append(f)
edit('quotient_fold.rs','// Included inside quotient_fold.', 'include!("r99_quotient.rs");\n// Included inside quotient_fold.')
edit('circle_norm.rs','impl Selected{','''impl Selected{
    pub(super) fn inverse_folded(&self,values:&[K],abc:[K;3],base:&[M31],lines:&[M31],alpha:K)->Result<Vec<K>,Error>{
        joined_inverse::inverse_folded(self,values,abc,base,lines,alpha)
    }''')
edit('joined_inverse.rs','fn batch_two(','''pub(super) fn inverse_folded(selected:&Selected,values:&[K],abc:[K;3],base:&[M31],lines:&[M31],alpha:K)->Result<Vec<K>,Error>{
    line_norm::inverse_folded(selected,values,abc,base,lines,alpha)
}
fn batch_two(''')
edit('line_norm.rs','pub(super) fn inverse(selected:&Selected,values:&[K],abc:[K;3],base:&[M31],lines:&[M31])->Result<(Vec<K>,Vec<M31>),Error>{',
'''#[path="r99_fold_inverse.rs"] mod folded;
pub(super) fn inverse_folded(selected:&Selected,values:&[K],abc:[K;3],base:&[M31],lines:&[M31],alpha:K)->Result<Vec<K>,Error>{
    folded::inverse(selected,values,abc,base,lines,alpha)
}
fn norm_inverse(selected:&Selected,values:&[K],abc:[K;3],base:&[M31],lines:&[M31])->Result<(Vec<CM31>,Vec<M31>),Error>{''')
edit('line_norm.rs','''    let out=values.iter().zip(norms).zip(inv).map(|((v,n),d)|{
        let ni=CM31::new(n.a.mul(d),n.b.neg().mul(d));
        K{c0:v.c0.mul(ni),c1:v.c1.neg().mul(ni)}
    }).collect();
    Ok((out,base_inv))
}''','''    let out=norms.into_iter().zip(inv).map(|(n,d)|CM31::new(n.a.mul(d),n.b.neg().mul(d))).collect();
    Ok((out,base_inv))
}
pub(super) fn inverse(selected:&Selected,values:&[K],abc:[K;3],base:&[M31],lines:&[M31])->Result<(Vec<K>,Vec<M31>),Error>{
    let (norms,base_inv)=norm_inverse(selected,values,abc,base,lines)?;
    let out=values.iter().zip(norms).map(|(v,ni)|K{c0:v.c0.mul(ni),c1:v.c1.neg().mul(ni)}).collect();
    Ok((out,base_inv))
}''')
f=ex/'r17_host_relation.rs';s=f.read_text();start=s.index('pub(super) fn opened_channel(');end=s.index('// New-profile verifier suffix.',start)
body=s[start:end]
old='let inverse_batch=selected_points.inverse_lines(&denoms,p.abc,&base_denoms,&lines);'
assert body.count(old)==1;body=body.replace(old,'let inverse_batch=selected_points.inverse_folded(&denoms,p.abc,&base_denoms,&lines,alpha);')
body=body.replace('let canonical=quotient_fold::Canonical::new(alpha,iv);','let canonical=quotient_fold::Weighted::new(iv);')
old='''            if let (Some(canonical),Ok((inverses,base_inverses)))=(&canonical,&inverse_batch) {
                let inv:[K;4]=inverses[4*i..4*i+4].try_into().unwrap();
                if let Some(folded)=canonical.divided(all,inv,if p.use_x{base.x}else{base.y},
                    p.use_x,base_inverses[2*i],base_inverses[2*i+1]) {'''
new='''            if let (Some(canonical),Ok(inverses))=(&canonical,&inverse_batch) {
                let weights:[K;4]=inverses[4*i..4*i+4].try_into().unwrap();
                if let Some(folded)=canonical.fold(all,weights,if p.use_x{base.x}else{base.y},p.use_x) {'''
assert body.count(old)==1;body=body.replace(old,new)
old='''                    .mul(match &inverse_batch {
                        Ok((inverses,_))=>inverses[4*i+slot],
                        Err(_)=>denoms[4*i+slot].try_inv().ok_or(Error::Domain)?,
                    });'''
assert body.count(old)==1;body=body.replace(old,'''                    // Fallback needs ordinary inverses, NEVER the folded weights.
                    .mul(denoms[4*i+slot].try_inv().ok_or(Error::Domain)?);''')
old='''            let (ix,iy)=match &inverse_batch {
                Ok((_,base_inverses))=>(base_inverses[2*i],base_inverses[2*i+1]),
                Err(_)=>(base.x.double().inv(),base.y.double().inv()),
            };'''
assert body.count(old)==1;body=body.replace(old,'''            let (ix,iy)=(base.x.double().inv(),base.y.double().inv());''')
f.write_text(s[:start]+body+s[end:]);changed.append(f)
f=ex/'performance-host/Cargo.toml';f.write_text(f.read_text()+'\n[[bin]]\nname="r99-fold-check"\npath="../r99_fold_check.rs"\n');changed.append(f)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r99_fold']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'private_arithmetic':a.private,
 'protocol_changed':False,'validation_removed':False,'new_security_claim':False,'selected':False,
 'contract':'Same internally derived circle points, chord values and line coordinates; fold weights multiply conjugate chord before norm inversion.'}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files']),'changed':len(set(changed))}))
