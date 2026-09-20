#!/usr/bin/env python3
"""Authenticated R16 reconstruction -> NEW, host-only R17 research profile.

No existing directory is overwritten. No deployment, wallet, or live adapter.
All source edits and shared modules are hashed in the output manifest.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from reconstruct_generated_inputs import EXPERIMENTS, one_replace

PROFILE = 'AV8/R17/structuredG271-two-channel/research-v1'


def function_body(text, signature, change):
    assert text.count(signature) == 1, signature
    start = text.index('{', text.index(signature))
    depth, end = 1, start + 1
    while depth:
        depth += (text[end] == '{') - (text[end] == '}')
        end += 1
    return text[:start+1] + change(text[start+1:end-1]) + text[end-1:]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    if out.exists():
        parser.error('output must be a new directory')
    subprocess.run([sys.executable, str(Path(__file__).with_name('stage_r16_basis_host.py')),
                    '--repo', str(args.repo.resolve()), '--output', str(out)], check=True)
    metadata = json.loads((out/'r16-stage.json').read_text())
    assert '--cfg v8_performance_sbf' not in metadata['rustflags']
    edits = []

    def edit(name, transform):
        path = out/EXPERIMENTS/name
        before = path.read_bytes()
        after = transform(before.decode()).encode()
        path.write_bytes(after)
        edits.append(dict(path=str(EXPERIMENTS/name),
            before_sha256=hashlib.sha256(before).hexdigest(), after_sha256=hashlib.sha256(after).hexdigest()))

    def root(s):
        s = one_replace(s, 'mod r16_basis_transport;', '''mod r16_basis_transport;
use r16_basis_transport as basis_transport;
mod r17_structured_g;
use r17_structured_g as structured_g;
mod r17_opening_weights;
use r17_opening_weights as opening_weights;
mod r17_host_relation;
use r17_host_relation as r17_relation;''', 'R17 shared modules')
        s = one_replace(s, 'const FIXED:usize=697;', 'const FIXED:usize=953;', 'Final512 frame')
        return one_replace(s, 'b.len()>40282', 'b.len()>44378', 'Final512 length bound')
    edit('relation_callback.rs', root)
    edit('inactive_row_binding.rs', lambda s: one_replace(s, 'fn to_gamma(',
        'pub(super) fn to_gamma(', 'reuse identical component/challenge prefix'))

    correction = '''
    let value=value.sub(claims[27].mul(corelib::state_only_hiding::state_only_explicit_g_mask_factor(z))).add(claims[27]);
'''

    def payment(s):
        s = one_replace(s, 'AV8/R16/basis89-dual-dense/research-v1', PROFILE, 'R17 prover profile')
        old = '''fn point_rows(messages:&[Vec<K>],z:&[K;10])->Vec<K>{
    corelib::v6_transcript::v6_statement_points(z).iter().flat_map(|p|messages.iter().map(move|m|multilinear_evaluate_qm31(m,p).unwrap())).collect()
}'''
        new = '''fn point_rows_with_g(messages:&[Vec<K>],z:&[K;10],gc:&[K;271])->Vec<K>{
    let mut out:Vec<K>=corelib::v6_transcript::v6_statement_points(z).iter().flat_map(|p|messages.iter().map(move|m|multilinear_evaluate_qm31(m,p).unwrap())).collect();
    out[27]=crate::structured_g::mask_eval(gc,z);out
}
fn point_rows(messages:&[Vec<K>],z:&[K;10])->Vec<K>{
    point_rows_with_g(messages,z,&crate::structured_g::mixed_coins(&messages[27]))
}'''
        s = one_replace(s, old, new, 'structured first G point; other points retained')
        s = function_body(s, 'fn payment_terminal(', lambda b: one_replace(b,
            '}.unwrap();', '}.unwrap();'+correction, 'prover terminal G replacement'))
        signature = 'fn terminal(p:&impl PaymentInput,tr:&PoolV1PairLatePublicStatementV1,m:&[Vec<K>],z:&[K;10],s:&row::Semantic)->K'
        s = one_replace(s, signature, signature.replace('fn terminal(', 'fn terminal_with_g(').replace(')->K', ',gc:&[K;271])->K'), 'precomputed G context')
        s = function_body(s, 'fn terminal_with_g(', lambda b: one_replace(b,
            'point_rows(m,z)', 'point_rows_with_g(m,z,gc)', 'reuse fixed mixed coins'))
        wrapper = signature+'{terminal_with_g(p,tr,m,z,s,&crate::structured_g::mixed_coins(&m[27]))}\n'
        s = one_replace(s, 'fn start(', wrapper+'fn start(', 'historical wrapper retained')
        def producer(b):
            b = one_replace(b, 'terminal(p,tr,m,&z,&s)', 'terminal_with_g(p,tr,m,&z,&s,&gc)', 'enumeration uses cached fixed G')
            b = one_replace(b, 'terminal(p,tr,m,&s.z,&s)', 'terminal_with_g(p,tr,m,&s.z,&s,&gc)', 'final carry uses same G')
            return '\n    let gc=crate::structured_g::mixed_coins(&m[27]);'+b
        s = function_body(s, 'fn semantic_produce(', producer)
        s = function_body(s, 'fn semantic_negative_fixture(', producer)
        return s + '\ninclude!("r17_h1_semantic_audit.rs");\ninclude!("r17_coupled_audit.rs");\ninclude!("r17_c1_witness_audit.rs");\n'
    edit('payment_extraction.rs', payment)

    def verifier(s):
        s = one_replace(s, 'AV8/R16/basis89-dual-dense/research-v1', PROFILE, 'R17 verifier profile')
        s = function_body(s, 'pub(super) fn payment_terminal(', lambda b: one_replace(b,
            '}.map_err(|_|Error::Terminal)?;', '}.map_err(|_|Error::Terminal)?;'+correction, 'verifier terminal G replacement'))
        return function_body(s, 'fn verify_parsed(', lambda _: '''
    let s=semantic(w,binding,public,transition).map_err(|_|4u32)?;
    let prepared=crate::r17_relation::prepare(s,w).map_err(|_|5u32)?;
    let result=crate::r17_relation::verify(w,prepared,false);
    let s=semantic(w,binding,public,transition).map_err(|_|4u32)?;
    let prepared=crate::r17_relation::prepare(s,w).map_err(|_|5u32)?;
    let reference=crate::r17_relation::verify(w,prepared,true);
    assert_eq!(result,reference,"R17 complete deferred/dense outcome");
    result.map_err(|_|6u32)
''')
    edit('performance_verifier.rs', verifier)

    def performance(s):
        s = one_replace(s, 'let transition=compiled.public_statement;', '''let alternate=if std::env::var_os("ASPIS_R17_C1_WITNESS_AUDIT").is_some(){
            assert!(std::env::var_os("ASPIS_V8_LIVE_CONTEXT").is_none());
            assert!(std::env::var_os("ASPIS_V8_COMPLETE_CONTEXT").is_none());
            assert_eq!(positive_case,"honest");
            let mut other=witness;other.input.pair.selected_second=!other.input.pair.selected_second;
            let public=match payment{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>p,_=>panic!("fixture transfer only")};
            let other_compiled=compile_pool_v1_pair_forest_private_transfer_merged_c1_v1(&public,&other,authoritative,snapshot).unwrap();
            assert_eq!(other_compiled.public_statement,compiled.public_statement);
            Some((other,other_compiled))
        }else{None};
        let transition=compiled.public_statement;''','same-public alternate witness diagnostic')
        s = one_replace(s, 'let mut s=semantic_produce(&mut v,semantic_start(t.clone(),&b,initial,lambda,chi),&payment,&transition,&messages);',
            '''let mut s=semantic_produce(&mut v,semantic_start(t.clone(),&b,initial,lambda,chi),&payment,&transition,&messages);
        let h1_coordinates=if std::env::var_os("ASPIS_R17_H1_SEMANTIC_AUDIT").is_some() || std::env::var_os("ASPIS_R17_COUPLED_AUDIT").is_some(){Some(r17_h1_semantic_audit(&payment,&transition,&messages,&s))}else{None};''',
            'opt-in source H1 semantic map diagnostic')
        s = one_replace(s, 'let mut v=vec![K::ZERO;697];',
            'let mut v=vec![K::ZERO;FIXED];', 'allocate complete Final512 frame')
        s = one_replace(s, 'pub fn run(){', '''pub fn run(){
    if std::env::args().nth(1).as_deref()==Some("--audit-existing"){
        let dir=std::env::args().nth(2).unwrap();
        let public=std::fs::read(format!("{dir}/public.bin")).unwrap();
        let transition=std::fs::read(format!("{dir}/transition.bin")).unwrap();
        let binding:[u8;32]=std::fs::read(format!("{dir}/binding.bin")).unwrap().try_into().unwrap();
        let body=std::fs::read(format!("{dir}/proof-1.bin")).unwrap();
        assert_eq!(super::super::performance_verifier::verify(&body,&binding,&public,&transition),Ok(()));
        println!("R17_PUBLIC_PREFIX_ACCEPTED");return;
    }
    if std::env::args().nth(1).as_deref()==Some("--reject-existing"){
        let dir=std::env::args().nth(2).unwrap();
        let public=std::fs::read(format!("{dir}/public.bin")).unwrap();
        let transition=std::fs::read(format!("{dir}/transition.bin")).unwrap();
        let binding:[u8;32]=std::fs::read(format!("{dir}/binding.bin")).unwrap().try_into().unwrap();
        let body=std::fs::read(format!("{dir}/proof-1.bin")).unwrap();
        assert!(super::super::performance_verifier::verify(&body,&binding,&public,&transition).is_err());
        println!("R17_LEGACY_PROFILE_REJECTED");return;
    }
''', 'legacy profile rejection control')
        s = one_replace(s, 'let initial=state_only_initial_mask_claim(&trace,&masks.mask_only_c1,&masks.g).unwrap();',
            'let initial=crate::r17_relation::initial(state_only_initial_mask_claim(&trace,&masks.mask_only_c1,&masks.g).unwrap(),&masks.g);', 'new G Boolean sum')
        start = s.index('        let(mut p,ordinary,mut claim,_)=row::prepare(sem,&w,true).unwrap();')
        end = s.index('        let mut body=f::body(&v,&a,&b,&records,(&fa,&fb));', start)
        s = s[:start]+'''
        let prepared=crate::r17_relation::prepare(sem,&w).unwrap();
        let audit_kappa=prepared.public_audit[10];
        let crate::r17_relation::Prepared{mut p,iv_g,mut weights,mut claim,..}=prepared;
        assert_eq!(p.gamma,gamma);
        let gp=gamma.pow(27);let mut qeval=[Vec::new(),Vec::new()];
        for(i,pt)in pts.iter().enumerate(){for(slot,(x,y))in[(pt.x,pt.y),(pt.x,pt.y.neg()),(pt.x.neg(),pt.y.neg()),(pt.x.neg(),pt.y)].into_iter().enumerate(){
            let all=(0..29).rev().fold(K::ZERO,|acc,col|acc.mul(gamma).add(if col<26{K::from_cm31(CM31::from_m31(encoded[col][4*i+slot]))}else{c2encoded[col-26][4*i+slot]}));
            let g=gp.mul(c2encoded[1][4*i+slot]);let l=p.abc[0].add(p.abc[1].mul_m31(x)).add(p.abc[2].mul_m31(y));
            for c in 0..2{let iv=if c==0{p.iv}else{iv_g};let value=if c==0{all.sub(g)}else{g};
                qeval[c].push(value.sub(iv[0].add(iv[1].mul_m31(if p.use_x{x}else{y}))).mul(l.try_inv().unwrap()));}
        }}
        let q=[decoder.solve_wide(&qeval[0]),decoder.solve_wide(&qeval[1])];
        for c in 0..2{assert_eq!(q[c][1023],K::ZERO);assert_eq!(p.abc[1].mul(q[c][1022]).sub(p.abc[2].mul(q[c][1021])),K::ZERO);}
        let first=crate::r17_relation::polynomial(&q,&weights);
        assert_eq!(corelib::sumcheck::boundary_sum(&first),claim);
        f::save_round(&mut v,0,first);absorb_round(&mut p.t,0,&first);
        p.t.absorb(label::M31_CIRCLE_FOLD_POW_NONCE,&[0;9]);
        let alpha=sample(&mut p.t,false).unwrap();claim=evaluate(&first,alpha);
        for c in 0..2{weights[c].fold_deferred_relation_arity4(alpha);}
        let mut finals=[primal(&q[0],alpha),primal(&q[1],alpha)];
        v[441..697].copy_from_slice(&finals[0]);v[697..953].copy_from_slice(&finals[1]);
        let nonces=[0u8;24];let stress_attempts=0u64;
        let(queries,rho)=query_schedule(&mut p,&v[441..953],&nonces).unwrap();
        if let Some((other,other_compiled))=&alternate{
            let base:Vec<Vec<M31>>=(0..16).map(|c|(0..1024).map(|r|other_compiled.semantic_c1.c1[c][r].sub(compiled.semantic_c1.c1[c][r])).collect()).collect();
            assert_eq!(base[3][1014],M31::ZERO);
            let delta=r17_c1_witness_audit(&base,&s.z,p.points,&queries,&enc);
            let mut corrected=trace.clone();for c in 0..16{for r in 0..1024{corrected.c1[c][r]=corrected.c1[c][r].add(delta[c][r]);}}
            let public=match payment{PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>p,_=>panic!("fixture transfer only")};
            assert_eq!(we::extract_checked(&corrected,&public,&transition,authoritative).unwrap(),*other);
            let before=aspis_statement::pool_v1::pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1(&compiled.trace,snapshot.next_pair_index,lambda,chi).unwrap();
            let after=aspis_statement::pool_v1::pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1(&other_compiled.trace,snapshot.next_pair_index,lambda,chi).unwrap();
            let changed=before.iter().zip(&after).filter(|(a,b)|a!=b).count();
            let h1_ood_delta=r17_h1_witness_ood_audit(&before,&after,p.points);
            let h1_joint_delta=r17_h1_witness_joint_audit(&h1_ood_delta,&delta,&s.z,&p,alpha,&queries,&enc,&decoder);
            let total_pad:Vec<_>=(0..1024).map(|r|h1_joint_delta[r].sub(after[r].sub(before[r]))).collect();
            let mut applied_pad=vec![K::ZERO;1024];apply_pool_v1_pair_forest_h1_padding_mask_v1(&mut applied_pad,&total_pad).unwrap();assert_eq!(applied_pad,total_pad);
            println!("R17_C1_WITNESS_VALIDATED same_public=true opposite_selected_input=true actual_helper_rebuilt=true helper_changed_rows={changed} fixed_prefix_diagnostic_only=true");
        }
        if std::env::var_os("ASPIS_R17_COUPLED_AUDIT").is_some(){r17_coupled_audit::run(h1_coordinates.as_ref().unwrap(),&s.z,&p,audit_kappa,alpha,&queries,|delta|{
            let codeword=enc.encode_c2_message(&crate::r16_basis_transport::transport().forward(delta)).unwrap();
            for &id in &queries{for slot in 0..4{assert_eq!(codeword[4*id as usize+slot],K::ZERO);}}
        });}
        let records:Vec<u8>=queries.iter().flat_map(|&id|{let i=id as usize;let mut r=c1leaf(&encoded,i);r.extend(c2leaf(&c2encoded,i,false));r.extend(salts[i]);r}).collect();
        let fa=f::frontier(&a,&queries);let fb=f::frontier(&b,&queries);
        let mut stub=f::body(&v,&a,&b,&records,(&fa,&fb));
        stub[FIXED*16+52..HEAD].copy_from_slice(&nonces);let w=parse(&stub).unwrap();
        let(values,xs)=crate::r17_relation::opened(&w,&p,iv_g,&queries,alpha).unwrap();
        for c in 0..2{for i in 0..Q{assert_eq!(values[c][i],corelib::v6_onefold::evaluate_final256_coefficients(&finals[c],xs[i]).unwrap());}}
        let inc=crate::r17_relation::inject_two(&mut weights,&mut claim,&values,&xs,rho).unwrap();p.t.absorb(label::PROFILE,&bytes(&[inc]));
        for r in 1..4{let poly=crate::r17_relation::polynomial(&finals,&weights);assert_eq!(corelib::sumcheck::boundary_sum(&poly),claim);
            f::save_round(&mut v,r,poly);absorb_round(&mut p.t,r,&poly);let a=sample(&mut p.t,false).unwrap();claim=evaluate(&poly,a);
            for c in 0..2{weights[c].fold_deferred_relation_arity4(a);finals[c]=primal(&finals[c],a);}}
''' + s[end:]
        s = one_replace(s, 'for index in [0,HEAD,body.len()-1] {',
            'for index in [0,HEAD,body.len()-1,417*16,441*16,697*16] {', 'retain and extend corruption controls')
        s = one_replace(s, '        std::fs::write(format!("{out}/proof-{seed}.bin"),&body).unwrap();\n        println!("PERF',
            '''        let mut noncanonical=body.clone();noncanonical[697*16..697*16+4].copy_from_slice(&corelib::field::P.to_le_bytes());
        assert!(verify(&noncanonical).is_err());
        std::fs::write(format!("{out}/proof-{seed}.bin"),&body).unwrap();
        println!("R17_CONTROL semantic_rounds=10 final_values=512 corrupted_bytes=6 noncanonical_g_final=true truncated=true deferred_dense_agree=true");
        println!("PERF''', 'canonical G field gate before publication')
        return s.replace('40282','44378')
    edit('performance.rs', performance)

    shared=[]
    for name in ['r17_structured_g.rs','r17_opening_weights.rs','r17_host_relation.rs','r17_h1_semantic_audit.rs','r17_coupled_audit.rs','r17_c1_witness_audit.rs']:
        data=Path(__file__).with_name(name).read_bytes()
        (out/EXPERIMENTS/name).write_bytes(data)
        shared.append(dict(path=str(EXPERIMENTS/name),sha256=hashlib.sha256(data).hexdigest()))
    metadata.update(r17_edits=edits,r17_shared=shared,profile=PROFILE,
        source_revision=metadata['source_revision'],diagnostic_only=True,privacy_proved=False,
        soundness_preservation_proved=False,scope='Selected isolated R17 host only: structured G, two quotient channels, Final512; no deployment adapter')
    (out/'r17-stage.json').write_text(json.dumps(metadata,indent=2)+'\n')
    print(json.dumps({'stage':str(out),'profile':PROFILE,'changes':edits,'shared':shared},indent=2))


if __name__=='__main__':
    main()
