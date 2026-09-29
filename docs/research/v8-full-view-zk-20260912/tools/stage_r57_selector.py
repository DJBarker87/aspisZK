#!/usr/bin/env python3
"""Generate a profile-local selector gather from the frozen endpoint registry."""
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
assert sha(src/'r18-stage.json')=='c2f16a9063dbf24580b1537fef0bffac4c3081276fe41774be01f83c28b4e5e9'
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==188
for n,h in m['files'].items():assert sha(src/n)==h,n
copy_path='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs'
constants_path='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs'
assert sha(src/copy_path)=='50062fff8b6afbffad3ddbb8eda09992353a9171c4955151cece26a654c6a6d5'
assert sha(src/constants_path)=='cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50'
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
path=dst/copy_path;s=path.read_text()
old=function(s,'pub(crate) fn evaluate_with_selectors(')
start=old.index('    let mut link_index = 0usize;');loop=function(old[start:],'while link_index <')
end=old.index(loop)+len(loop)
condition='all(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit", feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit")'
new=old[:start]+f'    #[cfg(not({condition}))]\n    {{\n'+old[start:end]+'\n    }\n'+f'    #[cfg({condition})]\n    r57_gather(&mut selector_tensor_scratch, selectors, append_index, variant);'+old[end:]
s=s.replace(old,new)
s+='\n#[cfg(not(v8_performance_sbf))]\n'+old.replace('fn evaluate_with_selectors(','fn r57_reference_evaluate(')+'\n'
s+=f'#[cfg({condition})]\ninclude!("r57_selector_gather.rs");\n'
path.write_text(s);helper=path.parent/'r57_selector_gather.rs';shutil.copy2(here/helper.name,helper)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';test=ex/'r57_selector_check.rs'
reference=ex/'r57_reference_copy.rs';shutil.copy2(src/copy_path,reference)
test.write_text('''fn main(){let (terms,weights,cases)=aspis_statement::pool_v1::pair_forest_copy_terminal::r57_selector_controls();
println!("R57_SELECTOR source_terms={terms} weight_checks={weights} scratch_and_full_lane_cases={cases} both_variants=true arbitrary_high_low=true original_source=true");}
''')
cargo=ex/'performance-host/Cargo.toml';cargo.write_text(cargo.read_text()+'\n[[bin]]\nname="r57-selector-check"\npath="../r57_selector_check.rs"\n')
for f in [path,helper,test,cargo,reference,dst/constants_path]:m['files'][str(f.relative_to(dst))]=sha(f)
m['r57_selector']={'base_revision':'80aa7d98ebbc708ef54b947bb1810b913ddd21ec','control_manifest_sha256':sha(src/'r18-stage.json'),
    'source_registry_unchanged':True,'source_derived_const_table':True,'protocol_changed':False}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
