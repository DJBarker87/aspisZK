#!/usr/bin/env python3
"""Isolated, HOST-ONLY R84 source-prefix screening profile.

No compact T163 evaluator is advertised as correct for this new transport.
The prefix producer uses its existing dense functional; execution stops after
the actual opposite-witness H1 check. No complete proof or CU result is claimed.
"""
import argparse, ast, hashlib, json, re, shutil
from pathlib import Path

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--control',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--dependency-diagnostic',action='store_true')
p.add_argument('--repair-tail',action='store_true')
a=p.parse_args();src=a.control;dst=a.output;here=Path(__file__).parent
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
ex=dst/'docs/research/v8-no-work-100-20260907/experiments'
changed=[]
def edit(n,fn):
    f=ex/n;f.write_text(fn(f.read_text()));changed.append(f)
def once(s,old,new):
    assert s.count(old)==1,(old,s.count(old));return s.replace(old,new)
base=lambda j:(j&1)|(((j>>1)&63)<<4)|(((j>>7)^7)<<1)
order=[base(j) for j in range(1024)]
assert order[127]==1023 and order[1023]==1009
order[127],order[1023]=order[1023],order[127]
if a.repair_tail:
    assert order[126]==1022 and order[1021]==993
    order[126],order[1021]=order[1021],order[126]
assert sorted(order)==list(range(1024)) and order[1023]==1023
assert order[:89]==[16*(j//2)+14+(j%2) for j in range(89)]
def tables(s):
    match=re.search(r'ORDER: \[usize; 1024\] = (\[[^;]+\]);',s)
    old=ast.literal_eval(match[1]);assert len(old)==1024
    return s[:match.start(1)]+str(order)+s[match.end(1):]
edit('r17_basis_tables.rs',tables)
def transport(s):
    start=s.index('        let pads: Vec<_> = (0..PIVOT)')
    end=s.index('        Self { order, inactive }',start)
    replacement='''        let base=|j:usize|(j&1)|(((j>>1)&63)<<4)|(((j>>7)^7)<<1);
        let mut order:Vec<_>=(0..N).map(base).collect();
        order.swap(127,1023);
        assert_eq!(order[PIVOT],PIVOT);
        for j in 0..PADS {
            let row=order[j];
            assert_eq!(row,16*(j/2)+14+(j%2));
            assert!(inactive[row] && legal(row) && row!=1014 && row!=PIVOT);
        }
        assert_eq!(order.as_slice(),fixed::ORDER.as_slice(),"host/source versus frozen SBF order");
'''
    if a.repair_tail:replacement=replacement.replace('        order.swap(127,1023);','        order.swap(127,1023);\n        order.swap(126,1021);')
    return s[:start]+replacement+s[end:]
edit('r16_basis_transport.rs',transport)
old=m['profile'];assert old=='AV8/R19/sparseG-T163/quadratic-channel-fold/research-v1'
profile='AV8/R84/sparseG-bitperm-swap/quadratic-channel-fold/research-v1'
if a.repair_tail:profile='AV8/R84/sparseG-bitperm-two-swaps/quadratic-channel-fold/research-v2'
for n in ['performance_verifier.rs','payment_extraction.rs']:
    edit(n,lambda s:once(s,old,profile))
edit('r17_host_relation.rs',lambda s:once(once(s,
    'AV8/R19/compact-functional/sparseG-T163/channel-fold/v1',
    'AV8/R84/functional/'+('sparseG-bitperm-two-swaps/channel-fold/v2'if a.repair_tail else'sparseG-bitperm-swap/channel-fold/v1')),
    'AV8/R19/four-image-residuals/pre-channel/v1','AV8/R84/four-image-residuals/pre-channel/'+('v2'if a.repair_tail else'v1')))
# Diagnostics precede, and do not weaken, the existing acceptance assertions.
def audit(s):
    if a.dependency_diagnostic:
        anchor='    let mut reduced=matrix.clone();for i in 0..562{reduced[i].push(target[i]);}'
        s=once(s,anchor,(here/'r84_h1_dependency.rs').read_text()+'\n'+anchor)
    return once(s,'    let pivots=reduce(&mut reduced,1022);assert_eq!(pivots.len(),540);',
'''    let pivots=reduce(&mut reduced,1022);
    let incompatible=reduced[pivots.len()..].iter().filter(|r|r[1022]!=K::ZERO).count();
    println!("R84_H1_SOURCE_SCREEN rank={} expected_rank=540 equations=562 affine_nonzero_residuals={} actual_opposite_witness=true",pivots.len(),incompatible);
    assert_eq!(pivots.len(),540);''')
edit('r17_c1_witness_audit.rs',audit)
def producer(s):
    anchor='            let total_pad:Vec<_>=(0..1024).map(|r|h1_joint_delta[r].sub(after[r].sub(before[r]))).collect();'
    s=once(s,anchor,'''            if std::env::var_os("ASPIS_R84_H1_PREFLIGHT").is_some() && std::env::var_os("ASPIS_R84_THROUGH_G").is_none() {
                println!("R84_H1_PREFLIGHT_PASS actual_source_prefix=true complete_proof=false privacy_proved=false");
                std::process::exit(0);
            }
'''+anchor)
    marker='            println!("R17_C1_WITNESS_VALIDATED same_public=true opposite_selected_input=true actual_helper_rebuilt=true helper_changed_rows={changed} fixed_prefix_diagnostic_only=true");'
    return once(s,marker,marker+'''
            if std::env::var_os("ASPIS_R84_THROUGH_G").is_some() {
                println!("R84_FULL_AFFINE_PREFLIGHT_PASS actual_source_prefix=true complete_proof=false privacy_proved=false");
                std::process::exit(0);
            }
''')
edit('performance.rs',producer)
shutil.copy2(here/'r84_bitperm_check.rs',ex/'r84_bitperm_check.rs');changed.append(ex/'r84_bitperm_check.rs')
edit('performance-host/Cargo.toml',lambda s:s+'\n[[bin]]\nname="r84-bitperm-check"\npath="../r84_bitperm_check.rs"\n')
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
for n in ['performance-sbf/Cargo.toml']:
    f=ex/n;m['files'][str(f.relative_to(dst))]=sha(f)
m['profile']=profile
m['r84_bitperm']={'control_manifest_sha256':sha(src/'r18-stage.json'),
    'host_only_preflight':True,'protocol_changed':True,'compact_verifier_integrated':False,
    'source_coverage_proved':False,'security_promoted':False,'expected_h1_rank':540,
    'source_revision':'d137f7316e0878bfb90780c13214a7586287deb2',
    'dependency_diagnostic':a.dependency_diagnostic,
    'extra_tail_swap':a.repair_tail,
    'unchanged_negative':'r18-pack negative_affine_T_H1_M31 rank517 retained'}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps({'stage':str(dst),'profile':profile,'pins':len(m['files']),'host_only':True}))
