#!/usr/bin/env python3
"""Clone a fully pinned R19 stage; apply opt-in, protocol-identical R20 rewrites.

Only source trees, manifests and pinned files are copied. Build outputs and
keys stay at their original location. No pin may disappear during cloning.
"""
import argparse
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

EX = Path('docs/research/v8-no-work-100-20260907/experiments')

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def replace_once(text, old, new):
    assert text.count(old) == 1, old[:100]
    return text.replace(old, new, 1)

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--stage', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--opening', action='store_true')
    p.add_argument('--checker', action='store_true')
    p.add_argument('--clean', action='store_true', help='remove CU checkpoints, not validation')
    p.add_argument('--digest', action='store_true')
    p.add_argument('--digest-check', action='store_true')
    p.add_argument('--whole-dot-check', action='store_true')
    p.add_argument('--dot-micro', action='store_true', help='arithmetic-only ELF, NOT a verifier')
    p.add_argument('--shared-prepare', action='store_true')
    p.add_argument('--shared-geometry', action='store_true')
    p.add_argument('--fine-profile', action='store_true')
    p.add_argument('--semantic-basis', action='store_true')
    p.add_argument('--sparse-whole', action='store_true')
    p.add_argument('--sparse-check', action='store_true')
    p.add_argument('--private-dot', action='store_true')
    p.add_argument('--private-field-check', action='store_true')
    p.add_argument('--factored', action='store_true', help='optional R19 factored T163 experiment')
    p.add_argument('--factored-packet', type=Path)
    a = p.parse_args()
    assert not (a.private_dot and a.whole_dot_check), 'run the dual-backend checker in its separate micro stage'
    src, dst = a.stage.resolve(), a.output.resolve()
    assert not dst.exists() and src not in dst.parents
    meta = json.loads((src/'r18-stage.json').read_text())
    assert meta['profile'] == 'AV8/R19/sparseG-T163/quadratic-channel-fold/research-v1'
    for n, h in meta['files'].items():
        f = (src/n).resolve()
        assert src in f.parents and digest(f) == h, n
    dst.mkdir()
    for n in ('crates', 'docs', 'programs', 'xtask'):
        if (src/n).exists():
            shutil.copytree(src/n, dst/n, ignore=shutil.ignore_patterns('target', '.git'))
    for n in ('Cargo.toml', 'Cargo.lock', 'r17-stage.json', 'r17-sbf-probe.json'):
        shutil.copy2(src/n, dst/n)
    for n in ('audit/poseidon-pair-probe/program/Cargo.toml', 'audit/poseidon-pair-probe/program/src/lib.rs'):
        if (src/n).is_file():
            (dst/n).parent.mkdir(parents=True,exist_ok=True)
            shutil.copy2(src/n,dst/n)
    for n, h in meta['files'].items():
        f = dst/n
        if not f.exists():
            f.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src/n, f)
        assert digest(f) == h, n
    changed = []
    if a.opening:
        path = dst/EX/'query_arithmetic.rs'
        text = path.read_text()
        begin = text.index('#[inline(never)]\npub(super) fn gamma(')
        end = text.index('\n// Same six four-product chunks', begin)
        combined = text[begin:end].replace('fn gamma(', 'fn combine_beta(')
        combined = combined.replace('powers:&StateOnlySpendQueryPowers', 'powers:&BetaCoefficients')
        combined = combined.replace('powers.base.c1_limbs', 'powers.c1_limbs')
        combined = combined.replace('&[powers.base.helpers[0],powers.base.helpers[1],powers.d]', '&powers.helpers')
        constructor = '''
// Coefficients, deliberately NOT represented as successive gamma powers.
pub(super) struct BetaCoefficients {
    c1_limbs: [[u32;4];26],
    helpers: [corelib::field::PreparedQm31Multiplier;3],
}
impl BetaCoefficients {
    pub(super) fn new(gamma:K,beta:K)->Self {
        let powers=corelib::field::qm31_power_table::<29>(gamma);
        let left=K::ONE.sub(beta);
        let c1_limbs=core::array::from_fn(|i| {
            let v=left.mul(powers[i]);
            [v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0]
        });
        let helpers=core::array::from_fn(|i|corelib::field::PreparedQm31Multiplier::new(
            (if i==1 {beta} else {left}).mul(powers[26+i])));
        Self{c1_limbs,helpers}
    }
}
'''
        path.write_text(text + constructor + combined)
        changed.append(path)
        path = dst/EX/'r17_host_relation.rs'
        text = path.read_text()
        start = text.index('pub(super) fn opened_channel(')
        before, body = text[:start], text[start:]
        body = replace_once(body, '    let powers = StateOnlySpendQueryPowers::new(p.gamma);\n    let gp = p.gamma.pow(27);',
            '    let powers = query_arithmetic::BetaCoefficients::new(p.gamma,beta);\n    let iv = crate::r19_channel_fold::interpolant(p.iv,iv_g,beta);')
        begin = body.index('        // This selected decoder validates ALL C1/C2 limbs')
        end = body.index('        entries.push((', begin)
        body = body[:begin] + '''        // Decode every limb even when its coefficient is zero (beta=0 or 1).
        let all = query_arithmetic::combine_beta(&r[..403], &r[403..589], &powers)?;
        #[cfg(not(target_os="solana"))] {
            let original=StateOnlySpendQueryPowers::new(p.gamma);
            let old=gamma_combine_v6_packed_layer0(&r[..403],&r[403..589],&original).map_err(|_|Error::Canonical)?;
            for slot in 0..4 {
                let g=p.gamma.pow(27).mul(corelib::v6_onefold::packed_qm31_at(&r[403..589],4+slot).unwrap());
                assert_eq!(all[slot],crate::r19_channel_fold::combined_raw(old[slot],g,beta));
            }
        }
''' + body[end:]
        body = replace_once(body, '            let iv = crate::r19_channel_fold::interpolant(p.iv,iv_g,beta);\n', '')
        body = replace_once(body, 'let v=crate::r19_channel_fold::combined_raw(all[slot],gv[slot],beta);', 'let v=all[slot];')
        path.write_text(before+body)
        changed.append(path)
    if a.shared_prepare:
        path = dst/EX/'r17_host_relation.rs'
        text = path.read_text()
        text = replace_once(text, '    let mut ordinary = [Vec::new(), Vec::new()];\n    for channel in 0..2 {',
            '    let mut ordinary = [Vec::new(), Vec::new()];\n    let shared_pair=if !dense_ordinary {crate::r17_compact_prepare::ordinary_pair(&s.z,kappa,use_x)} else {[K::ZERO;2]};\n    for channel in 0..2 {')
        text = replace_once(text, '            let mut pair=crate::r17_compact_prepare::ordinary_pair(&s.z,kappa,use_x);',
            '            let mut pair=shared_pair;')
        path.write_text(text)
        changed.append(path)
    if a.shared_geometry:
        path = dst/EX/'r17_weighted_groups.rs'
        text = path.read_text()
        text += '\nimpl Kernel { pub(super) fn geometry_parts(&self)->(&[K;16],&[K;3],&[K;16]) {(&self.normal,&self.carry,&self.high)} }\n'
        path.write_text(text); changed.append(path)
        path = dst/EX/'r19_channel_ordinary.rs'
        text = path.read_text()
        at = text.index('pub(super) fn terminal(')
        copy = text[at:]
        copy = replace_once(copy,'fn terminal(', 'fn terminal_shared(')
        copy = replace_once(copy,'    workspace: &mut [K],\n', '    workspace: &mut [K],\n    kernel: &r17_weighted_groups::Kernel,\n')
        copy = replace_once(copy,'    let kernel=r17_weighted_groups::Kernel::new(abc,alpha);\n','')
        copy = replace_once(copy,'&mut sums[..128],&kernel,inactive,pivot,true', '&mut sums[..128],kernel,inactive,pivot,true')
        path.write_text(text+'\n#[inline(never)]\n'+copy); changed.append(path)
        path = dst/EX/'r18_compact_g.rs'
        text = path.read_text()
        text += '''
#[inline(never)]
pub(super) fn terminal_shared(z:&[K;10],kernel:&super::r17_weighted_groups::Kernel,workspace:&mut[K])->[K;4] {
    assert!(workspace.len()>=399);
    let (coins,sums)=workspace.split_at_mut(271);
    super::r18_sparse_coded_g::coin_weights_into(z,coins);
    let (normal,carry,high)=kernel.geometry_parts();
    super::r18_sparse_coded_g::sparse_terminal(coins,normal,carry,high,sums)
}
'''
        path.write_text(text); changed.append(path)
        path = dst/EX/'r17_host_relation.rs'
        text = path.read_text()
        text = replace_once(text,
            '        let ordinary=crate::r19_channel_ordinary::terminal(&public_audit,p.abc,alphas,beta,&mut workspace);',
            '        let kernel=crate::r17_weighted_groups::Kernel::new(p.abc,alphas);\n        let ordinary=crate::r19_channel_ordinary::terminal_shared(&public_audit,p.abc,alphas,beta,&mut workspace,&kernel);')
        text = replace_once(text,'crate::r18_compact_g::terminal(&z,p.abc,alphas,&mut workspace)',
            'crate::r18_compact_g::terminal_shared(&z,&kernel,&mut workspace)')
        path.write_text(text); changed.append(path)
    if a.semantic_basis:
        assert a.shared_geometry
        for name in ('r20_whole_dot.rs','r20_semantic_basis.rs'):
            path=dst/EX/name
            shutil.copy2(Path(__file__).with_name(name),path); changed.append(path)
        path=dst/EX/'relation_callback.rs'
        path.write_text(path.read_text()+'\nmod r20_whole_dot;\nmod r20_semantic_basis;\n'); changed.append(path)
        path=dst/EX/'performance_verifier.rs'
        text=path.read_text()
        header="fn semantic(w:&Wire<'_>,binding:&[u8;32],public:&PoolV1PairForestTerminalPaymentV1,transition:&PoolV1PairLatePublicStatementV1)->Result<row::Semantic,Error>{"
        replacement="""fn semantic(w:&Wire<'_>,binding:&[u8;32],public:&PoolV1PairForestTerminalPaymentV1,transition:&PoolV1PairLatePublicStatementV1)->Result<row::Semantic,Error>{
    semantic_cached(w,binding,public,transition,&mut [])
}
#[inline(never)]
fn semantic_cached(w:&Wire<'_>,binding:&[u8;32],public:&PoolV1PairForestTerminalPaymentV1,transition:&PoolV1PairLatePublicStatementV1,cache:&mut[K])->Result<row::Semantic,Error>{
    assert!(cache.is_empty() || cache.len()==271);"""
        text=replace_once(text,header,replacement)
        old='''        #[cfg(not(v8_block_horner))] {s.claim=evaluate_state_only_polynomial(&poly,s.z[r]);}
        #[cfg(v8_block_horner)] {s.claim=semantic_eval(&poly,s.z[r]);}'''
        new='''        if cache.is_empty() {
            #[cfg(not(v8_block_horner))] {s.claim=evaluate_state_only_polynomial(&poly,s.z[r]);}
            #[cfg(v8_block_horner)] {s.claim=semantic_eval(&poly,s.z[r]);}
        } else {
            // Cache is verifier-owned and freshly derived AFTER this round's challenge.
            s.claim=crate::r20_semantic_basis::evaluate_round(s.claim,sent.try_into().unwrap(),s.z[r],
                (&mut cache[1+27*r..1+27*(r+1)]).try_into().unwrap());
            #[cfg(not(target_os="solana"))]
            assert_eq!(s.claim,evaluate_state_only_polynomial(&poly,s.z[r]));
        }'''
        text=replace_once(text,old,new)
        text=replace_once(text,'    checkpoint("v8:semantic-rounds");','''    if !cache.is_empty() {
        let mut scale=M31::ONE;
        for r in (0..10).rev() {
            for v in &mut cache[1+27*r..1+27*(r+1)] {*v=v.mul_m31(scale);}
            scale=scale.mul(corelib::field::M31_HALF);
        }
        cache[0]=K::ONE.mul_m31(scale);
        #[cfg(not(target_os="solana"))] {
            let mut original=vec![K::ZERO;271];
            crate::r18_sparse_coded_g::coin_weights_into(&s.z,&mut original);
            assert_eq!(cache,original.as_slice(),"actual ten-challenge G cache");
        }
    }
    checkpoint("v8:semantic-rounds");''')
        # Only the first (primary) call receives the cache. Independent reference stays old.
        at=text.index('fn verify_parsed(')
        before,body=text[:at],text[at:]
        old='    let s=semantic(w,binding,public,transition).map_err(|_|4u32)?;'
        assert body.count(old)==2
        body=body.replace(old,'    let mut semantic_basis=vec![K::ZERO;271];\n    let s=semantic_cached(w,binding,public,transition,&mut semantic_basis).map_err(|_|4u32)?;',1)
        body=replace_once(body,'    let result=crate::r17_relation::verify(w,prepared,false);',
            '    let result=crate::r17_relation::verify_cached(w,prepared,false,Some(&semantic_basis));')
        path.write_text(before+body); changed.append(path)
        path=dst/EX/'r17_host_relation.rs'
        text=path.read_text()
        old="pub(super) fn verify(w:&Wire<'_>,prepared:Prepared,reference:bool)->Result<(),Error>{"
        text=replace_once(text,old,old+'''\n    verify_cached(w,prepared,reference,None)
}
pub(super) fn verify_cached(w:&Wire<'_>,prepared:Prepared,reference:bool,coins:Option<&[K]>)->Result<(),Error>{''')
        text=replace_once(text,'        let sparse=crate::r18_compact_g::terminal_shared(&z,&kernel,&mut workspace);',
            '''        let sparse=if let Some(coins)=coins {
            let (normal,carry,high)=kernel.geometry_parts();
            crate::r18_sparse_coded_g::sparse_terminal(coins,normal,carry,high,&mut workspace)
        }else{crate::r18_compact_g::terminal_shared(&z,&kernel,&mut workspace)};''')
        path.write_text(text); changed.append(path)
    if a.sparse_whole:
        for name in ('r20_whole_dot.rs','r20_sparse_whole.rs'):
            path=dst/EX/name
            shutil.copy2(Path(__file__).with_name(name),path); changed.append(path)
        path=dst/EX/'relation_callback.rs'
        text=path.read_text()
        if 'mod r20_whole_dot;' not in text: text+='\nmod r20_whole_dot;\n'
        text+='\nmod r20_sparse_whole;\n'
        path.write_text(text); changed.append(path)
        path=dst/EX/'r18_compact_g.rs'
        text=path.read_text()
        assert 'super::r18_sparse_coded_g::sparse_terminal' in text
        text=text.replace('super::r18_sparse_coded_g::sparse_terminal','super::r20_sparse_whole::sparse_terminal')
        path.write_text(text); changed.append(path)
        if a.semantic_basis:
            path=dst/EX/'r17_host_relation.rs'
            text=replace_once(path.read_text(),'crate::r18_sparse_coded_g::sparse_terminal(coins,normal,carry,high,&mut workspace)',
                'crate::r20_sparse_whole::sparse_terminal(coins,normal,carry,high,&mut workspace)')
            path.write_text(text); changed.append(path)
        if a.sparse_check:
            path=dst/EX/'r20_sparse_check.rs'
            path.write_text('''extern crate aspis_core as corelib;
mod r18_sparse_coded_g;
mod r20_whole_dot;
mod r20_sparse_whole;
fn main(){
    r20_sparse_whole::differential_check(r18_sparse_coded_g::sparse_terminal);
    println!("R20_SPARSE_WHOLE source_reference=R18 cases=295 all271bases=true sums_equal=true");
}
'''); changed.append(path)
            path=dst/EX/'performance-host/Cargo.toml'
            path.write_text(path.read_text()+'\n[[bin]]\nname="r20-sparse-check"\npath="../r20_sparse_check.rs"\n'); changed.append(path)
    if a.checker:
        assert a.opening
        source = Path(__file__).with_name('r19_opening_check.rs').read_text()
        start, end = source.index('fn compare('), source.index('pub(super) fn run')
        source = source[:start] + '''fn compare(w:&Wire<'_>,p:&Prefix,g:[K;2],ids:&[u32],a:K)->Result<([Vec<K>;2],Vec<M31>),Error>{
    let old=r17_relation::opened(w,p,g,ids,a);
    for beta in [K::ZERO,K::ONE,K::ONE.neg(),p.gamma,p.iv[0],p.iv[1]] {
        let fresh=r17_relation::opened_channel(w,p,g,ids,a,beta);
        match (&old,&fresh) {
            (Ok((vs,xs)),Ok((v,x)))=>{
                assert_eq!(xs,x);
                assert_eq!(*v,vs[0].iter().zip(&vs[1]).map(|(&r,&g)|crate::r19_channel_fold::lerp(r,g,beta)).collect::<Vec<_>>());
            },
            (Err(x),Err(y))=>assert_eq!(x,y),
            _=>panic!("R20 opening/error mismatch: {old:?} {fresh:?}"),
        }
    }
    old
}
''' + source[end:]
        source = source.replace('R19_OPENING source_', 'R20_OPENING betas=6 source_')
        path = dst/EX/'r20_opening_check.rs'
        path.write_text(source)
        changed.append(path)
        path = dst/EX/'relation_callback.rs'
        text = replace_once(path.read_text(), '#[cfg(v8_performance)]\nfn main(){payment_extraction::performance::run();}',
            '#[cfg(all(v8_performance,not(r20_opening_check)))]\nfn main(){payment_extraction::performance::run();}')
        path.write_text(text+'\n#[cfg(r20_opening_check)]\nmod r20_opening_check;\n#[cfg(r20_opening_check)]\nfn main(){r20_opening_check::run();}\n')
        changed.append(path)
    if a.digest:
        path = dst/'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'
        text = path.read_text()
        text = replace_once(text, '    return public_digest_packed_selector_tensor(public, openings, selectors);',
            '    return r20_digest_factored::public_digest_packed_selector_tensor_r20(public, openings, selectors);')
        text += '\n#[path="r20_digest_factored.rs"]\nmod r20_digest_factored;\n'
        path.write_text(text)
        changed.append(path)
        copied = path.with_name('r20_digest_factored.rs')
        shutil.copy2(Path(__file__).with_name(copied.name), copied)
        changed.append(copied)
        if a.digest_check:
            text = path.read_text()
            anchor = '\n#[path="r20_digest_factored.rs"]'
            at = text.index(anchor)
            last = text.rfind('\n}', 0, at)
            assert last > text.index('mod tests {')
            text = text[:last] + '\n    include!("r20_digest_check.rs");\n' + text[last:]
            path.write_text(text)
            copied = path.with_name('r20_digest_check.rs')
            shutil.copy2(Path(__file__).with_name(copied.name), copied)
            changed.append(copied)
    if a.whole_dot_check or a.dot_micro or a.private_dot or a.private_field_check:
        packet = Path(__file__).resolve().parent.parent/'r20-pack/src'
        # Also support the focused NUC tools directory, without changing pins.
        if not packet.is_dir():
            packet = Path('/home/dombarker/project-offloads/aspis-r20-packet-20260922-a/src')
        packet_manifest=json.loads((packet.parent/'MANIFEST.json').read_text())
        for original,name in [('canonical.rs','r20_private_canonical.rs'),('whole_dot.rs','r20_private_dot.rs')]:
            assert digest(packet/original)==packet_manifest['files']['src/'+original]['sha256']
            path = dst/EX/name
            text = (packet/original).read_text()
            if original=='whole_dot.rs':
                text = replace_once(text,'use crate::canonical::','use super::canonical::')
            path.write_text(text); changed.append(path)
        path = dst/EX/'r20_private_dot_adapter.rs'
        shutil.copy2(Path(__file__).with_name(path.name),path); changed.append(path)
    if a.private_dot:
        assert a.semantic_basis or a.sparse_whole
        path=dst/EX/'relation_callback.rs'
        path.write_text(path.read_text()+'\nmod r20_private_dot_adapter;\n'); changed.append(path)
        if a.semantic_basis:
            path=dst/EX/'r20_semantic_basis.rs'
            text=replace_once(path.read_text(),'crate::r20_whole_dot::dot(a, b)', 'crate::r20_private_dot_adapter::dot(a, b)')
            path.write_text(text); changed.append(path)
        if a.sparse_whole:
            path=dst/EX/'r20_sparse_whole.rs'
            text=replace_once(path.read_text(),'use super::{corelib, r20_whole_dot};',
                'use super::{corelib, r20_private_dot_adapter as r20_whole_dot};')
            path.write_text(text); changed.append(path)
            if a.sparse_check:
                path=dst/EX/'r20_sparse_check.rs'
                path.write_text(path.read_text()+'\nmod r20_private_dot_adapter;\n'); changed.append(path)
    if a.whole_dot_check:
        for name in ('r20_whole_dot.rs','r20_whole_dot_check.rs','r20_semantic_basis.rs'):
            path = dst/EX/name
            shutil.copy2(Path(__file__).with_name(name),path)
            changed.append(path)
        path = dst/EX/'performance-host/Cargo.toml'
        path.write_text(path.read_text()+'\n[[bin]]\nname="r20-whole-dot-check"\npath="../r20_whole_dot_check.rs"\n')
        changed.append(path)
    if a.private_field_check:
        path=dst/EX/'r20_private_field_check.rs'
        shutil.copy2(Path(__file__).with_name(path.name),path); changed.append(path)
        path=dst/EX/'performance-host/Cargo.toml'
        path.write_text(path.read_text()+'\n[[bin]]\nname="r20-private-field-check"\npath="../r20_private_field_check.rs"\n'); changed.append(path)
    if a.dot_micro:
        assert not a.clean
        for name in ('r20_whole_dot.rs','r20_dot_micro.rs'):
            path = dst/EX/name
            shutil.copy2(Path(__file__).with_name(name),path)
            changed.append(path)
        path = dst/EX/'relation_callback.rs'
        text = path.read_text()
        old = '''    performance_verifier::verify(&body, instruction.try_into().unwrap(),
        &public, &transition).map_err(ProgramError::Custom)'''
        new = '''    // Arithmetic-only experiment: deliberately NOT verifier acceptance.
    let left:Vec<K>=(0..163).map(|i|K::from_le_bytes(&body[16*i..16*(i+1)]).unwrap()).collect();
    let right:Vec<K>=(0..163).map(|i|K::from_le_bytes(&body[16*(163+i)..16*(164+i)]).unwrap()).collect();
    for n in [3usize,4,6,16,27,163] {
        let mut reference=K::ZERO;
        for mode in 0..5u8 {
            solana_program::msg!("R20:dot-start n={} mode={}",n,mode);
            solana_program::log::sol_log_compute_units();
            let result=r20_dot_micro::run(core::hint::black_box(&left[..n]),core::hint::black_box(&right[..n]),core::hint::black_box(mode));
            solana_program::log::sol_log_compute_units();
            solana_program::msg!("R20:dot-end");
            if mode==0 {reference=result;} else {assert_eq!(reference,result);}
        }
    }
    Ok(())'''
        text = replace_once(text,old,new)
        path.write_text(text+'\nmod r20_dot_micro;\n')
        changed.append(path)
    if a.factored:
        assert a.shared_geometry
        from r20_factored_adapter import apply as apply_factored
        changed.extend(apply_factored(dst,a.factored_packet))
        path=dst/EX/'r19_channel_ordinary_check.rs'
        text=path.read_text()
        if a.sparse_whole: text+='\nmod r20_sparse_whole;\nmod r20_whole_dot;\n'
        if a.private_dot: text+='\nmod r20_private_dot_adapter;\n'
        path.write_text(text); changed.append(path)
        path=dst/EX/'performance-host/Cargo.toml'
        path.write_text(path.read_text()+'\n[[bin]]\nname="r20-factored-check"\npath="../r19_channel_ordinary_check.rs"\n'); changed.append(path)
    if a.fine_profile:
        assert not a.clean and not a.dot_micro
        patch = Path(__file__).with_name('r20_semantic_profile.patch')
        subprocess.run(['patch','--fuzz=0','-p1','-i',str(patch.resolve())],cwd=dst,check=True)
        changed.append(dst/'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs')
        probe = json.loads((dst/'r17-sbf-probe.json').read_text())
        probe['rustflags'] = probe['rustflags'].replace('--cfg v8_quiet_profile','')+' --cfg r20_fine_profile'
        (dst/'r17-sbf-probe.json').write_text(json.dumps(probe,indent=2)+'\n')
    removed_logs = 0
    if a.clean:
        for path in (dst/EX).rglob('*.rs'):
            text = path.read_text()
            # Only pure checkpoint arguments observed in the pinned stage.
            text, count = re.subn(r'solana_program::msg!\((?:"[^"\n]*"|name)\);', '();', text)
            text, cus = re.subn(r'solana_program::log::sol_log_compute_units\(\);', '();', text)
            if count or cus:
                path.write_text(text)
                changed.append(path)
                removed_logs += count + cus
        for path in (dst/EX).rglob('*.rs'):
            assert 'sol_log_compute_units' not in path.read_text(), path
        probe = json.loads((dst/'r17-sbf-probe.json').read_text())
        probe['diagnostic_instrumentation'] = False
        (dst/'r17-sbf-probe.json').write_text(json.dumps(probe,indent=2)+'\n')
    meta['r20_execution'] = {
        'base_git_commit': 'c9315d8b05efb2cdad976bb0f4db3574f1c24577',
        'input_manifest_sha256': digest(src/'r18-stage.json'),
        'opening_coefficients': a.opening, 'checker': a.checker,
        'digest_factored': a.digest, 'digest_checker': a.digest_check,
        'whole_dot_checker': a.whole_dot_check,
        'shared_preparation_pair': a.shared_prepare,
        'shared_terminal_geometry': a.shared_geometry,
        'arithmetic_only_not_verifier': a.dot_micro,
        'fine_profile': a.fine_profile,
        'semantic_basis_cache': a.semantic_basis,
        'sparse_whole_dot': a.sparse_whole,
        'sparse_checker': a.sparse_check,
        'private_canonical_dot': a.private_dot,
        'private_field_checker': a.private_field_check,
        'factored_T163_experiment': a.factored,
        'instrumented': not a.clean, 'removed_checkpoint_calls': removed_logs,
        'protocol_unchanged': True, 'built': False,
        'source_changes': {str(f.relative_to(dst)): {'before': meta['files'].get(str(f.relative_to(dst))), 'after':digest(f)} for f in changed},
    }
    for path in changed:
        meta['files'][str(path.relative_to(dst))] = digest(path)
    (dst/'r18-stage.json').write_text(json.dumps(meta,indent=2)+'\n')
    print(json.dumps({'stage':str(dst), 'changed':len(changed), 'pins':len(meta['files']), 'built':False}))

if __name__ == '__main__':
    main()
