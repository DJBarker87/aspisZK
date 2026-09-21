#!/usr/bin/env python3
"""Separate quadratic-channel research profile, never an R18 replacement."""
import argparse,hashlib,json,shutil
from pathlib import Path
from reconstruct_generated_inputs import EXPERIMENTS,one_replace
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
a=p.parse_args();assert not a.output.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((a.stage/'r18-stage.json').read_text())
assert m['basis_profile']=='minimum-support-163'
for n,h in m['files'].items():assert sha(a.stage/n)==h,n
shutil.copytree(a.stage,a.output);root=a.output/EXPERIMENTS
def edit(n,f):
    p=root/n;p.write_text(f(p.read_text()))
here=Path(__file__).resolve().parent
shutil.copy2(here.parent/'r19-pack/src/channel_fold.rs',root/'r19_channel_fold.rs')
edit('relation_callback.rs',lambda s:one_replace(one_replace(s,'const FIXED:usize=953;','const FIXED:usize=699;','699 fields'),
    'mod r18_shared_ordinary;','mod r18_shared_ordinary;\nmod r19_channel_ordinary;\nmod r19_channel_fold;','new compact modules').replace('b.len()>44378','b.len()>40314'))
old=m['profile'];profile='AV8/R19/sparseG-T163/quadratic-channel-fold/research-v1'
for n in ['performance_verifier.rs','payment_extraction.rs']:
    edit(n,lambda s:one_replace(s,old,profile,'new profile at initialization'))
edit('relation_callback_fixtures.rs',lambda s:one_replace(s,'pub(super) fn save_round(v:&mut[K],r:usize,p:[K;7]){v[417+r*6..423+r*6]',
 'pub(super) fn save_round(v:&mut[K],r:usize,p:[K;7]){v[419+r*6..425+r*6]','shift actual producer relation sent fields'))
# Same source tensor evaluator, change only first point scale and omit E work.
s=(root/'r18_shared_ordinary.rs').read_text()
assert 'split_at_mut(163)' in s and 'fn one_terminal(' in s
s=s.replace('alpha:[K;4],factors:', 'alpha:[K;4],beta:K,factors:')
s=s.replace('->([K;4],[K;4]) {','->[K;4] {')
s=s.replace('k.mul(raw[0][d])','K::ONE.sub(beta).mul(k).mul(raw[0][d])')
s=s.replace('    fill_tensor(&pairs[0],raw[0],&mut factors[160..240]);','')
s=s.replace('    let e=block_terminal_impl(&pairs[0],alpha,abc,None).0;','')
s=s.replace('(core::array::from_fn(|i|a[i].add(b[i])),e)','core::array::from_fn(|i|a[i].add(b[i]))')
s=s.replace('fn terminal_pair(', 'fn terminal(').replace('    workspace: &mut [K],','    beta: K,\n    workspace: &mut [K],').replace(') -> [[K; 4]; 2] {',') -> [K;4] {')
s=s.replace('let (plain_a,plain_e)=prepare_rows(audit,abc,alpha,','let plain_a=prepare_rows(audit,abc,alpha,beta,')
s=s.replace('    let e=one_terminal(factors,160,plain_e,delta,&mut sums[..128],&kernel,inactive,pivot,false);\n    [a,e]','    a')
(root/'r19_channel_ordinary.rs').write_text(s)
# Retain old opened() for independent host comparison; new source path folds once.
s=(root/'r17_host_relation.rs').read_text()
start=s.index('pub(super) fn opened(');end=s.index('\npub(super) fn polynomial',start)
opening=s[start:end]
assert 'opened_mode' not in opening, 'channel prototype starts from unmodified final R18 stage'
opening=opening.replace('fn opened(', 'fn opened_channel(',1).replace('    alpha: K,','    alpha: K,\n    beta: K,',1)
opening=opening.replace('Result<([Vec<K>; 2], Vec<M31>), Error>','Result<(Vec<K>,Vec<M31>),Error>',1)
opening=opening.replace('for channel in 0..2 {','for channel in 0..1 {')
opening=opening.replace('let iv = if channel == 0 { p.iv } else { iv_g };','let iv = crate::r19_channel_fold::interpolant(p.iv,iv_g,beta);')
opening=one_replace(opening,'''let v = if channel == 0 {
                    all[slot].sub(gv[slot])
                } else {
                    gv[slot]
                };''','let v=crate::r19_channel_fold::combined_raw(all[slot],gv[slot],beta);','combined numerator before fold')
start_ref=opening.index('    // Retain an independently implemented original combined-opening check.')
opening=opening[:start_ref]+'''    #[cfg(not(target_os="solana"))] {
        let (old,old_xs)=opened(w,p,iv_g,queries,alpha)?;
        assert_eq!(old_xs,xs);
        assert_eq!(values[0],old[0].iter().zip(&old[1]).map(|(&r,&g)|crate::r19_channel_fold::lerp(r,g,beta)).collect::<Vec<_>>());
    }
    Ok((core::mem::take(&mut values[0]),xs))
}
'''
s=s[:s.index('pub(super) fn verify(')]+opening+'\n'+here.joinpath('r19_channel_verify.rs').read_text()
s=s.replace('AV8/R18/compact-functional/code128-step3/minimalT163/two-channel/v2','AV8/R19/compact-functional/sparseG-T163/channel-fold/v1')
s=s.replace('AV8/R18/four-image-residuals/sparse-coded-minimalT-v2','AV8/R19/four-image-residuals/pre-channel/v1')
(root/'r17_host_relation.rs').write_text(s)
def producer(s):
    anchor='        let first=crate::r17_relation::polynomial(&q,&weights);'
    addition='''        let wr:Vec<_>=(0..1024).map(|i|weights[0].weight_at(i)).collect();
        let wg:Vec<_>=(0..1024).map(|i|weights[1].weight_at(i)).collect();
        let sent=crate::r19_channel_fold::prover_message(&q[0],&q[1],&wr,&wg).unwrap();
        v[417]=sent[0];v[418]=sent[1];
        let (beta,newclaim)=crate::r17_relation::channel_challenge(&mut p,claim,sent).unwrap();claim=newclaim;
        let original_q=q.clone();
        let combined_q:Vec<_>=q[0].iter().zip(&q[1]).map(|(&r,&g)|crate::r19_channel_fold::lerp(r,g,beta)).collect();
        let combined_w:Vec<_>=wr.iter().zip(&wg).map(|(&r,&g)|crate::r19_channel_fold::lerp(r,g,beta)).collect();
        assert_eq!(dot(&combined_q,&combined_w),claim,"channel boundary then beta");
        let q=[combined_q,vec![K::ZERO;1024]];
        weights=[WeightAccumulator::empty(10),WeightAccumulator::empty(10)];
        weights[0].add_dense(combined_w).unwrap();
'''
    s=one_replace(s,anchor,addition+anchor,'source channel prover')
    s=s.replace('v[441..697].copy_from_slice(&finals[0]);v[697..953].copy_from_slice(&finals[1]);','v[443..699].copy_from_slice(&finals[0]);')
    s=s.replace('&v[441..953]','&v[443..699]')
    s=one_replace(s,'r17_g_witness_audit(&semantic_delta,&rest_q_delta,&s.z,&p,audit_kappa,alpha,&queries,&enc)',
        'r17_g_witness_audit(&semantic_delta,&rest_q_delta,&s.z,&p,audit_kappa,alpha,beta,&queries,&enc)','new full-view affine gate')
    s=one_replace(s,'            for r in 0..1024{alternate_messages[27][r]=alternate_messages[27][r].add(g_delta[r]);}',
    '''            for r in 0..1024{alternate_messages[27][r]=alternate_messages[27][r].add(g_delta[r]);}
            // Independently reconstruct the G quotient difference from actual
            // encoded values and the existing decoder, not the matrix basis.
            let gc=enc.encode_c2_message(&crate::r16_basis_transport::transport().forward(&g_delta)).unwrap();
            let mut gv=Vec::new();
            for (i,pt) in pts.iter().enumerate(){for (slot,(x,y)) in [(pt.x,pt.y),(pt.x,pt.y.neg()),(pt.x.neg(),pt.y.neg()),(pt.x.neg(),pt.y)].into_iter().enumerate(){
                gv.push(gc[4*i+slot].mul(p.abc[0].add(p.abc[1].mul_m31(x)).add(p.abc[2].mul_m31(y)).try_inv().unwrap()));
            }}
            let gq=decoder.solve_wide(&gv);
            let qr:Vec<_>=original_q[0].iter().zip(&rest_q_delta).map(|(&a,&d)|a.add(d)).collect();
            let qg:Vec<_>=original_q[1].iter().zip(&gq).map(|(&a,&d)|a.add(gp.mul(d))).collect();
            assert_eq!(crate::r19_channel_fold::prover_message(&qr,&qg,&wr,&wg).unwrap(),sent,"both actual channel coefficients retained");
            let mut wb=WeightAccumulator::empty(10);wb.add_dense(wr.iter().zip(&wg).map(|(&r,&g)|crate::r19_channel_fold::lerp(r,g,beta)).collect()).unwrap();
            let qb:Vec<_>=qr.iter().zip(&qg).map(|(&r,&g)|crate::r19_channel_fold::lerp(r,g,beta)).collect();
            assert_eq!(polynomial_for_extension(&qb,&wb),first,"new first relation polynomial retained");
            assert_eq!(primal(&qb,alpha),finals[0],"new Final256 retained");
            println!("R19_CHANNEL_WITNESS source_p0_p2_retained=true first_relation_all7=true combined_final256=true decoder_independent=true fixed_prefix_only=true");''','independent new observation replay')
    anchor='let(values,xs)=crate::r17_relation::opened(&w,&p,iv_g,&queries,alpha).unwrap();'
    s=one_replace(s,anchor,anchor+'''
        let values=[values[0].iter().zip(&values[1]).map(|(&r,&g)|crate::r19_channel_fold::lerp(r,g,beta)).collect::<Vec<_>>(),vec![K::ZERO;Q]];''','prover query channel')
    s=s.replace('[0,HEAD,body.len()-1,417*16,441*16,697*16]','[0,HEAD,body.len()-1,417*16,418*16,443*16]')
    s=s.replace('noncanonical[697*16..697*16+4]','noncanonical[443*16..443*16+4]')
    s=s.replace('R17_CONTROL semantic_rounds=10 final_values=512','R19_CONTROL semantic_rounds=10 channel_fields=2 final_values=256 privacy_gate_open=true')
    return s
edit('performance.rs',producer)
def affine(s):
    # Modify only this profile's G leaf. C1/H1 source corrections and original
    # R18 repository regressions remain intact. Stronger separate-final zero
    # constraints are retained as a sufficient fixed-prefix screening gate.
    start=s.index('fn r17_g_witness_audit(');end=s.index('\n// First affine helper step',start)
    f=s[start:end]
    f=one_replace(f,'kappa: K, alpha: K, queries:', 'kappa: K, alpha: K, beta: K, queries:', 'new beta parameter')
    f=one_replace(f,'let rp=corelib::sumcheck::polynomial_for_extension(rq,&rw);\n    assert_eq!(corelib::sumcheck::boundary_sum(&rp),K::ZERO);',
    '''let wr:Vec<_>=(0..1024).map(|i|rw.weight_at(i)).collect();
    let wg:Vec<_>=(0..1024).map(|i|gw.weight_at(i)).collect();
    let dw:Vec<_>=wg.iter().zip(&wr).map(|(&g,&r)|g.sub(r)).collect();
    assert_eq!(dot(rq,&wr),K::ZERO,"new p0 affine target after C1/H1");
    let mut wb=WeightAccumulator::empty(10);
    wb.add_dense(wr.iter().zip(&wg).map(|(&r,&g)|crate::r19_channel_fold::lerp(r,g,beta)).collect()).unwrap();
    let rp=corelib::sumcheck::polynomial_for_extension(rq,&wb).map(|x|K::ONE.sub(beta).mul(x));''','literal mixed functional and p0')
    f=f.replace(';625]', ';626]').replace('0..625','0..626')
    f=one_replace(f,'let poly=corelib::sumcheck::polynomial_for_extension(&q,&gw);',
        'matrix[625][j]=dot(&dw,&q);\n        let poly=corelib::sumcheck::polynomial_for_extension(&q,&wb).map(|x|beta.mul(x));','new p2 row and mixed relation')
    f=one_replace(f,'let mut reduced=matrix.clone();',
        'target[625]=dot(&dw,rq).mul(scale.inv());\n    let mut reduced=matrix.clone();','p2 actual affine offset')
    f=f.replace('assert_eq!(pivots.len(),601);','let rank=pivots.len();')
    f=f.replace('reduced[601..]','reduced[rank..]')
    f=one_replace(f,'let gp=corelib::sumcheck::polynomial_for_extension(&q,&gw);',
        '''assert_eq!(scale.mul(dot(&dw,&q)),dot(&dw,rq),"new p2 source equation");
    let gp=corelib::sumcheck::polynomial_for_extension(&q,&wb).map(|x|beta.mul(x));''','all original mixed relation equations')
    f=f.replace('R17_G_WITNESS_JOINT equations=625 rank=601 compatibility_residuals=24',
        'R19_G_WITNESS_JOINT equations=626 rank={rank} new_p0_checked=true new_p2_checked=true')
    return s[:start]+f+s[end:]
edit('r17_c1_witness_audit.rs',affine)
m['r19_channel']={'input_profile':m['profile'],'pre_beta_extraction_proved':False,'new_message_privacy_proved':False,'fields':699}
m['profile']=profile;m['files'].update({str(p.relative_to(a.output)):sha(p) for p in sorted(root.glob('*.rs'))})
(a.output/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(a.output),'profile':profile,'privacy_proved':False}))
