#!/usr/bin/env python3
"""SECOND R18 profile: exact source first89, minimum 163-coordinate support.

Run only after first-profile source and SBF screening. Host constructor and
SBF tables are independently checked by the export gate before any SBF build.
"""
import argparse,ast,hashlib,json,re,shutil
from pathlib import Path
from reconstruct_generated_inputs import EXPERIMENTS,one_replace
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--first-profile-svm',type=Path,required=True)
a=p.parse_args();assert not a.output.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
meta=json.loads((a.stage/'r18-stage.json').read_text())
assert meta['compact_primary'] and meta['current_T_unchanged']
for name,expected in meta['files'].items():assert sha(a.stage/name)==expected,name
measurements=[json.loads(l) for l in a.first_profile_svm.read_text().splitlines() if l.startswith('{')]
assert any(r['case']=='honest' and r['accepted'] for r in measurements),'measured successful first primary required'
shutil.copytree(a.stage,a.output);root=a.output/EXPERIMENTS
oldprofile=meta['profile'];profile='AV8/R18/sparse-coded-G128-step3/minimal-T163/research-v2'
changes={}
def edit(name,fn):
    path=root/name;before=sha(path);path.write_text(fn(path.read_text()))
    changes[name]=dict(before_sha256=before,after_sha256=sha(path))
oldtable=(root/'r17_basis_tables.rs').read_text()
oldorder=ast.literal_eval(re.search(r'ORDER: \[usize; 1024\] = (\[[^;]+\]);',oldtable)[1])
assert len(oldorder)==1024 and sorted(oldorder)==list(range(1024))
pads=oldorder[:89];used=set(pads);order=list(range(1024));order[:89]=pads
missing=iter(i for i in range(89) if i not in used)
for hole in pads:
    if hole>=89:order[hole]=next(missing)
assert sorted(order)==list(range(1024)) and order[1023]==1023
support=[i for i in range(1024) if order[i]!=i]
assert len(support)==163 and order[:89]==pads
successors=[support.index(order[i]) for i in support]
(root/'r18_original_basis_tables.rs').write_text(oldtable)
(root/'r17_basis_tables.rs').write_text(oldtable.replace(str(oldorder),str(order),1))
(root/'r18_minimal_support.rs').write_text(
    f'pub const SUPPORT: [usize;163] = {support};\n'
    f'pub const NEXT: [usize;163] = {successors};\n')
for name in ['r18_minimal_transport.rs','r18_minimal_transport_check.rs']:
    shutil.copy2(Path(__file__).with_name(name),root/name)
def transport(s):
    s=one_replace(s,'use aspis_core::field::{M31, QM31};',
        'use aspis_core::field::{M31, QM31};\n#[cfg(not(target_os="solana"))]\n#[path="r18_minimal_transport.rs"] mod minimal;', 'host constructor source')
    return one_replace(s,'''        let mut order = pads.clone();
        order.extend((0..PIVOT).filter(|r| !pads.contains(r)));
        order.push(PIVOT);''','''        let order=minimal::minimal_order(pads.as_slice().try_into().unwrap())
            .expect("source legal unique pad inventory").to_vec();''','minimum-support completion')
edit('r16_basis_transport.rs',transport)
for name in ['performance_verifier.rs','payment_extraction.rs']:
    edit(name,lambda s:one_replace(s,oldprofile,profile,'second profile from initialization'))
edit('r17_host_relation.rs',lambda s:one_replace(one_replace(s,
    'AV8/R18/compact-functional/code128-step3/271-coins/two-channel/v1',
    'AV8/R18/compact-functional/code128-step3/minimalT163/two-channel/v2','basis descriptor'),
    'AV8/R18/four-image-residuals/sparse-coded-v1',
    'AV8/R18/four-image-residuals/sparse-coded-minimalT-v2','image domain'))
def ordinary(s):
    s=one_replace(s,'include!("r17_reused_block_terminal.rs");',
        'include!("r17_reused_block_terminal.rs");\ninclude!("r18_minimal_support.rs");','frozen exact support')
    s=one_replace(s,'fn cycle(delta:&mut[K], order:&[usize]) {',
        'fn cycle(delta:&mut[K], order:&[usize]) {','cycle anchor')
    s=s.replace('delta.len(),479','delta.len(),163').replace('[false;479]','[false;163]')
    s=s.replace('for start in 0..479','for start in 0..163').replace('let next=order[at];','let next=NEXT[at];')
    s=one_replace(s,'for j in 0..479 {delta[j]=entry(factors,off,j);}',
        'for j in 0..163 {delta[j]=entry(factors,off,SUPPORT[j]);}','evaluate only forced support')
    s=one_replace(s,'let d=kernel.prefix_into(delta,sums);',
        'let d=kernel.selected_into(&SUPPORT,delta,sums);','sparse correction contraction')
    s=one_replace(s,'workspace.split_at_mut(479)','workspace.split_at_mut(163)','163 workspace')
    return s
edit('r18_shared_ordinary.rs',ordinary)
edit('r17_weighted_groups.rs',lambda s:s+'''
// Fixed public support; no value-dependent selection or new allocation.
impl Kernel {
    pub(super) fn selected_into(&self,rows:&[usize],values:&[K],sums:&mut[K])->[K;4] {
        assert_eq!(rows.len(),values.len());assert!(sums.len()>=128);
        sums[..128].fill(K::ZERO);
        for (&row,&value) in rows.iter().zip(values) {
            let group=row>>4;let low=row&15;
            sums[2*group]=sums[2*group].add(value.mul(self.normal[low]));
            if low<3 {sums[2*group+1]=sums[2*group+1].add(self.prepared_carry[low].mul(value));}
        }
        self.contract(|j|(sums[2*j],sums[2*j+1]))
    }
}
''')
# The old compact-ordinary host helper assumes the 479-cycle but remains a
# valid dense-prefix reference for this smaller-support permutation. Primary
# uses only the separately generated SUPPORT/NEXT entries above.
manifest=root/'performance-host/Cargo.toml'
manifest.write_text(manifest.read_text()+'''\n[[bin]]
name="r18-minimal-transport-check"
path="../r18_minimal_transport_check.rs"
''')
meta.update(profile=profile,current_T_unchanged=False,basis_profile='minimum-support-163',
    minimal_changes=changes,first_profile_svm_sha256=sha(a.first_profile_svm),
    source_gates_passed=False,sbf_measured=False)
meta['files'].update({str(p.relative_to(a.output)):sha(p) for p in sorted(root.glob('*.rs'))})
(a.output/'r18-stage.json').write_text(json.dumps(meta,indent=2)+'\n')
host=json.loads((a.output/'r17-stage.json').read_text());host['profile']=profile
(a.output/'r17-stage.json').write_text(json.dumps(host,indent=2)+'\n')
print(json.dumps(dict(stage=str(a.output),profile=profile,support=len(support))))
