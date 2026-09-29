#!/usr/bin/env python3
"""Exact-output ordinary-tensor experiments on the selected R82 source."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--variant',choices=['tensor','blockdot','opt2','opts','packed','packed-block'],default='tensor');a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='f70d74f4e479899b7eda0664a4dfdf4b8e8068d7bf9be836a2cd681397167498'
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==210
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():
        (dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';changed=[]
# Strengthen the frozen closure: prior manifests did not include the separate
# SBF Cargo profile. Pin it explicitly without altering any runtime source.
sbf_cargo=ex/'performance-sbf/Cargo.toml';sbf_name=str(sbf_cargo.relative_to(dst))
assert sbf_name not in m['files'];m['files'][sbf_name]=sha(sbf_cargo)
if a.variant in ['opt2','opts']:
    cargo=ex/'performance-sbf/Cargo.toml';old=cargo.read_text();needle='opt-level = 3'
    assert old.count(needle)==1 and 'overflow-checks = true' in old
    name=str(cargo.relative_to(dst));assert name in m['files']
    control_cargo_hash=sha(cargo)
    cargo.write_text(old.replace(needle,'opt-level = '+('2'if a.variant=='opt2'else'"s"')))
    m['files'][name]=sha(cargo);assert len(m['files'])==211
    m['r83_native']={'control_manifest_sha256':sha(src/'r18-stage.json'),'variant':a.variant,
        'control_sbf_manifest_sha256':control_cargo_hash,'protocol_changed':False,
        'validation_removed':False,'selected':False,'overflow_checks':True}
    (dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
    (dst/'host-reuse.json').write_text(json.dumps({'source_stage':str(src),
        'source_manifest_sha256':sha(src/'r18-stage.json'),
        'host_environment_sha256':sha(src/'r24-host-a/environment.json'),
        'wire_controls_sha256':sha(src/'r24-host-a/wire-controls/results.json'),
        'unchanged_original_source_pins':210,'host_replayed':False,
        'reason':'Only the separately rooted SBF release optimization level changed; host source and build settings are identical.'},indent=2)+'\n')
    print(json.dumps({'stage':str(dst),'pins':len(m['files']),'variant':a.variant}));raise SystemExit
if a.variant in ['packed','packed-block']:
    query=ex/'query_arithmetic.rs';v=query.read_text()
    old='    helpers: [corelib::field::PreparedQm31Multiplier;3],'
    assert v.count(old)==1;v=v.replace(old,old+'\n    mixed: [[u32;4];12],')
    old='''        let helpers=core::array::from_fn(|i|corelib::field::PreparedQm31Multiplier::new(
            (if i==1 {beta} else {left}).mul(powers[26+i])));
        Self{c1_limbs,helpers}'''
    new='''        let raw:[K;3]=core::array::from_fn(|i|(if i==1 {beta} else {left}).mul(powers[26+i]));
        let helpers=raw.map(corelib::field::PreparedQm31Multiplier::new);
        let columns=raw.map(r83_matrix);
        let mixed=core::array::from_fn(|i|columns[i/4][i%4]);
        Self{c1_limbs,helpers,mixed}'''
    assert v.count(old)==1;v=v.replace(old,new)
    start=v.index('pub(super) fn combine_beta(');begin=v.index('    let mut out=[K::ZERO;4];',start)
    end=v.index('// Caller-owned decoded storage',begin)
    new='''    let mut out=[K::ZERO;4];
    for slot in 0..4 {
        let values:&[u32;26]=c1[26*slot..26*(slot+1)].try_into().unwrap();
        let f=[r83_mixed_limb::<0>(values,c2,slot,powers),r83_mixed_limb::<1>(values,c2,slot,powers),
            r83_mixed_limb::<2>(values,c2,slot,powers),r83_mixed_limb::<3>(values,c2,slot,powers)];
        out[slot]=K{c0:CM31::new(f[0],f[1]),c1:CM31::new(f[2],f[3])};
    }
    Ok(out)
}

'''
    query.write_text(v[:begin]+new+v[end:]+'\n'+(here/'r83_packed.rs').read_text());changed.append(query)
    check=ex/'r55_opening_check.rs';v=check.read_text();needle='query_arithmetic::r55_controls();'
    assert v.count(needle)==1
    check.write_text(v.replace(needle,needle+'query_arithmetic::r83_packed_controls();'));changed.append(check)
    if a.variant=='packed-block':
        ordinary=ex/'r19_channel_ordinary.rs';v=ordinary.read_text()
        start=v.index('fn prepare_rows_scalar(');end=v.index('include!("r22_scalar.rs")',start)
        part=v[start:end];assert part.count('block_terminal_scalar_impl(')==2
        ordinary.write_text(v[:start]+part.replace('block_terminal_scalar_impl(','r83_block_terminal(')+v[end:]+'\n'+(here/'r83_block_dot.rs').read_text());changed.append(ordinary)
        check=ex/'r27_check.rs';v=check.read_text();needle='    for world in 0..2 {';assert v.count(needle)==1
        check.write_text(v.replace(needle,'    println!("R83_BLOCK_DOT source_vectors=256 genuine_inputs=2 original_block_terminal_retained=true");\n'+needle));changed.append(check)
    for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
    assert len(m['files'])==211
    m['r83_native']={'control_manifest_sha256':sha(src/'r18-stage.json'),'variant':a.variant,
        'protocol_changed':False,'validation_removed':False,'selected':False}
    (dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
    print(json.dumps({'stage':str(dst),'pins':len(m['files']),'variant':a.variant}));raise SystemExit
ordinary=ex/'r19_channel_ordinary.rs';v=ordinary.read_text()
start=v.index('fn prepare_rows_scalar(');end=v.index('include!("r22_scalar.rs")',start)
part=v[start:end]
if a.variant=='tensor':
    assert part.count('fill_tensor_support(')==2
    part=part.replace('fill_tensor_support(','r83_fill_tensor(')
else:
    assert part.count('block_terminal_scalar_impl(')==2
    part=part.replace('block_terminal_scalar_impl(','r83_block_terminal(')
v=v[:start]+part+v[end:]
ordinary.write_text(v+'\n'+(here/('r83_tensor.rs'if a.variant=='tensor'else'r83_block_dot.rs')).read_text());changed.append(ordinary)
native=ex/'r27_native.rs';v=native.read_text();needle='r19_channel_ordinary::r27_tensor_check(x);'
assert v.count(needle)==1
if a.variant=='tensor':
    native.write_text(v.replace(needle,needle+'r19_channel_ordinary::r83_tensor_check(x);'));changed.append(native)
check=ex/'r27_check.rs';v=check.read_text();needle='    for world in 0..2 {';assert v.count(needle)==1
tag='R83_TENSOR complementary_profiles=256 general_fallback_profiles=256 scalar_and_blocks=51200 poison_slots_retained=true'if a.variant=='tensor'else'R83_BLOCK_DOT source_vectors=256 genuine_inputs=2 original_block_terminal_retained=true'
check.write_text(v.replace(needle,f'    println!("{tag}");\n'+needle));changed.append(check)
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
assert len(m['files'])==211
m['r83_native']={'control_manifest_sha256':sha(src/'r18-stage.json'),'variant':a.variant,
    'protocol_changed':False,'validation_removed':False,'selected':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
