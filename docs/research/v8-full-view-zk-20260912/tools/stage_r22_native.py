#!/usr/bin/env python3
"""Source-locked R20 native scalar experiment; no auxiliary proof code runs."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--profile',action='store_true')
a=p.parse_args();src=a.control.resolve();dst=a.output.resolve();here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def function(text,needle):
    start=text.index(needle);brace=text.index('{',start);depth=0
    for i in range(brace,len(text)):
        depth+=(text[i]=='{')-(text[i]=='}')
        if depth==0:return text[start:i+1]
    raise ValueError(needle)
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==173 and not m['r20_execution']['instrumented']
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','audit/poseidon-pair-probe/program/Cargo.toml','audit/poseidon-pair-probe/program/src/lib.rs',*m['files']]:
    if n.startswith('audit/') and not(src/n).exists():continue
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
for n in ['r22_scalar.rs','r22_check.rs','r22_sbf.rs']:
    shutil.copy2(here/n,ex/n);changed.append(ex/n)
# Pure reference interface only; no R21 prover, circuit or verifier is copied.
native=(here/'r21_native.rs').read_text()
native=native.replace('//! R21 host-only native public-arithmetic relation.','//! R22 exact native ordinary/image comparison. No auxiliary proof.')
native=native.replace('    let kernel = r17_weighted_groups::Kernel::new(abc, alpha);','    r22_tick("native.start");\n    let kernel = r17_weighted_groups::Kernel::new(abc, alpha);\n    r22_tick("native.chord_geometry");')
native=native.replace('    ordinary_dot.add(image)','    let result=ordinary_dot.add(image);r22_tick("native.image_and_dot");result')
candidate=function(native,'pub fn compute(').replace('pub fn compute(','pub fn compute_scalar(',1)
candidate=candidate.replace('vec![K::ZERO; 1024]','vec![K::ZERO; 531]')
candidate=candidate.replace('r19_channel_ordinary::terminal_shared(','r19_channel_ordinary::terminal_scalar(').replace('        beta,\n        &mut workspace,','        beta,\n        &finals,\n        &mut workspace,')
candidate=candidate.replace('qm31_sum_products4(ordinary, finals)','ordinary')
native+='\n#[inline(never)]\n'+candidate+'\n'
native+='''
#[inline(always)] pub(super) fn r22_tick(label:&str) {
    #[cfg(all(target_os="solana",r22_profile))] {solana_program::log::sol_log(label);solana_program::log::sol_log_compute_units();}
    #[cfg(not(all(target_os="solana",r22_profile)))] let _=label;
}
#[cfg(not(target_os="solana"))] pub fn check_adjoint(x:&[K;24]) {
    r19_channel_ordinary::adjoint_check(x[11..14].try_into().unwrap(),x[14..18].try_into().unwrap(),&x[19..23].try_into().unwrap());
}
'''
(ex/'r22_native.rs').write_text(native);changed.append(ex/'r22_native.rs')
path=ex/'r19_channel_ordinary.rs';ordinary=path.read_text()
prepare=function(ordinary,'fn prepare_rows(')
block=function((ex/'r17_reused_block_terminal.rs').read_text(),'fn block_terminal_impl(')
block=block.replace('fn block_terminal_impl(','fn block_terminal_scalar_impl(').replace('block1:Option<[K;4]>)->([K;4],usize)','block1:Option<[K;4]>,finals:&[K;4])->K')
at=block.index('    let out = core::array::from_fn(')
block=block[:at]+'''    let mut result=common.mul(corelib::field::qm31_sum_products4(z,*finals))
        .add(active.mul(corelib::field::qm31_sum_products4(stop,*finals)));
    for _ in 0..8 {result=result.half();}
    let _=count;result
}'''
scalar=prepare.replace('fn prepare_rows(','fn prepare_rows_scalar(').replace('factors:&mut[K])->[K;4]','factors:&mut[K],finals:&[K;4])->K')
scalar=scalar.replace('block_terminal_impl(','block_terminal_scalar_impl(').replace('Some(blocks[0])).0','Some(blocks[0]),finals)').replace('Some(blocks[1])).0','Some(blocks[1]),finals)')
scalar=scalar.replace('core::array::from_fn(|i|a[i].add(b[i]))','a.add(b)')
# Identical instrumentation in both preparation organizations; compiled away in clean build.
def instrument_prepare(t):
    t=t.replace('    fill_tensor(&pairs[0]', '    super::r22_tick("prepare.point_factors");\n    fill_tensor(&pairs[0]',1)
    t=t.replace('    let a=block_terminal','    super::r22_tick("prepare.tensor_factors");\n    let a=block_terminal',1)
    t=t.replace('\n    core::array::from_fn(|i|a[i].add(b[i]))','\n    super::r22_tick("prepare.plain_contraction");\n    core::array::from_fn(|i|a[i].add(b[i]))')
    t=t.replace('\n    a.add(b)','\n    super::r22_tick("prepare.plain_contraction");\n    a.add(b)')
    return t
ordinary=ordinary.replace(prepare,instrument_prepare(prepare))
ordinary=ordinary.replace('    cycle(delta,&t.order);','    super::r22_tick("reference.permutation_values");\n    cycle(delta,&t.order);')
ordinary=ordinary.replace('    let wp=entry(factors,off,1023);','    super::r22_tick("reference.permutation_contract");\n    let wp=entry(factors,off,1023);')
ordinary=ordinary.replace('    let pivot=kernel.coordinate(1023);','    super::r22_tick("reference.inactive");\n    let pivot=kernel.coordinate(1023);')
ordinary+='\n'+block+'\n'+instrument_prepare(scalar)+'\ninclude!("r22_scalar.rs");\n'
path.write_text(ordinary);changed.append(path)
path=ex/'performance-host/Cargo.toml';path.write_text(path.read_text()+'\n[[bin]]\nname="r22-check"\npath="../r22_check.rs"\n');changed.append(path)
path=ex/'performance-sbf/Cargo.toml';text=path.read_text();assert text.count('path = "../relation_callback.rs"')==1
path.write_text(text.replace('path = "../relation_callback.rs"','path = "../r22_sbf.rs"'));changed.append(path)
for p in changed:m['files'][str(p.relative_to(dst))]=sha(p)
m['r22_native']={'control_manifest_sha256':sha(src/'r18-stage.json'),'control_source_pins':173,'profile':a.profile,'auxiliary_proof':False,'protocol_changed':False,'source_files':{str(p.relative_to(dst)):sha(p)for p in changed}}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
probe=json.loads((dst/'r17-sbf-probe.json').read_text())
if a.profile:probe['rustflags']+=' --cfg r22_profile'
(dst/'r17-sbf-probe.json').write_text(json.dumps(probe,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'profile':a.profile,'source_pins':len(m['files'])}))
