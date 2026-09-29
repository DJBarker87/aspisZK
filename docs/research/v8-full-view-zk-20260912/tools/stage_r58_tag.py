#!/usr/bin/env python3
"""Exact source-tag decomposition; paired pattern correction, isolated stage."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def function(s,needle):
    start=s.index(needle);brace=s.index('{',start);depth=0
    for i in range(brace,len(s)):
        depth+=(s[i]=='{')-(s[i]=='}')
        if depth==0:return s[start:i+1]
    raise AssertionError(needle)
assert sha(src/'r18-stage.json')=='2653b3555389aee79eb4866ed94d74131247eb574dd972b07f166c558c491435'
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==193
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
path=dst/'crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';s=path.read_text()
tag=function(s,'fn copy_tag_coordinate_dot(');finish=function(s,'fn finish_selector_tensor_basis(');reference=function(s,'pub(crate) fn r57_reference_evaluate(')
condition='all(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit", feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit")'
brace=tag.index('{')
new_tag=tag[:brace+1]+f'\n    #[cfg({condition})]\n    {{ r58_tag_delta(coordinate, selectors) }}\n    #[cfg(not({condition}))]\n    {{'+tag[brace+1:-1]+'\n    }\n}'
brace=finish.index('{')
shift=f'''\n    #[cfg({condition})]
    let mut shifted_patterns = *patterns;
    #[cfg({condition})]
    for pattern in &mut shifted_patterns {{ pattern.c0.a = pattern.c0.a.add(M31(R58_TAG_BASE)); }}
    #[cfg({condition})]
    let patterns = &shifted_patterns;
'''
s=s.replace(tag,new_tag).replace(finish,finish[:brace+1]+shift+finish[brace+1:])
s=s.replace(reference,reference.replace('finish_selector_tensor_basis(', 'r58_reference_finish('))
reference_cfg=f'#[cfg(all(not(v8_performance_sbf), {condition}))]'
s+='\n'+reference_cfg+'\n'+tag.replace('fn copy_tag_coordinate_dot(','fn r58_reference_tag_dot(')+'\n'
s+='\n'+reference_cfg+'\n'+finish.replace('fn finish_selector_tensor_basis(','fn r58_reference_finish(').replace('copy_tag_coordinate_value(','r58_reference_tag_value(')+'\n'
s+='\n'+reference_cfg+'''
fn r58_reference_tag_value(_scratch:&[QM31],coordinate:usize,selectors:&Selectors)->QM31 {
    r58_reference_tag_dot(coordinate,selectors)
}
'''
s+=f'#[cfg({condition})]\ninclude!("r58_tag_base.rs");\n';path.write_text(s)
helper=path.parent/'r58_tag_base.rs';shutil.copy2(here/helper.name,helper)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';test=ex/'r58_tag_check.rs'
test.write_text('''fn main(){let (terms,weights,cases)=aspis_statement::pool_v1::pair_forest_copy_terminal::r57_selector_controls();
println!("R57_SELECTOR source_terms={terms} weight_checks={weights} scratch_and_full_lane_cases={cases} original_tag_and_finish=true");
let (tags,finishes,negatives)=aspis_statement::pool_v1::pair_forest_copy_terminal::r58_tag_controls();
println!("R58_TAG coordinate_checks={tags} finish_checks={finishes} omitted_base_negative_cases={negatives} four_limb_basis=true source_reference=true");}
''')
cargo=ex/'performance-host/Cargo.toml';cargo.write_text(cargo.read_text()+'\n[[bin]]\nname="r58-tag-check"\npath="../r58_tag_check.rs"\n')
for f in [path,helper,test,cargo]:m['files'][str(f.relative_to(dst))]=sha(f)
m['r58_tag']={'base_revision':'e6e2015650ba4104da3797e4c375591ba29e92c0','control_manifest_sha256':sha(src/'r18-stage.json'),
    'tag_base':1124073472,'maximum_delta':135,'paired_pattern_correction':True,'protocol_changed':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
