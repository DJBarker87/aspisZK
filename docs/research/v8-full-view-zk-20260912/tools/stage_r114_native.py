#!/usr/bin/env python3
"""Compile all fixed Copy-tag linear forms together, preserving every tag."""
import argparse,ast,collections,hashlib,json,re,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(src/'r18-stage.json')=='1455a58e904b3b803c46de43686c73733b5c58a69f1bf391cc5d5190fbb1a296'
m=json.loads((src/'r18-stage.json').read_text())
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:
    shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';folder=dst/'crates/aspis-statement/src/pool_v1';changed=[]
def save(f,s):f.write_text(s);changed.append(f)
f=folder/'pair_forest_copy_terminal.rs';source=f.read_text();registry=(folder/'pair_forest_copy_terminal_constants.rs').read_text()
def array(name):return ast.literal_eval(re.search(r'const '+name+r':[^=]+=\s*(\[[^;]+\]);',source)[1])
group=list(zip(array('COPY_GROUP_LOCAL_COORDINATE_GROUPS'),array('COPY_GROUP_LOCAL_COORDINATE_LOCALS')));assert len(group)==30
pat=r'CompiledPoolV1PairForestLink \{ tag: (\d+), weight_kind: (\d+), weight_level: (\d+), producer: CompiledPoolV1PairForestEndpoint \{ row: (\d+), slot: (\d+), pattern: (\d+) \}, consumer: CompiledPoolV1PairForestEndpoint \{ row: (\d+), slot: (\d+), pattern: (\d+) \} \}'
links=[list(map(int,x))for x in re.findall(pat,registry)];assert len(links)==136
rows=[[]for _ in range(30)]
for i,(tag,kind,level,*ends)in enumerate(links):
    assert tag==1124073472+i
    for side in range(2):
        row,slot,pattern=ends[3*side:3*side+3];rows[group.index((2*side+slot,row&15))].append((row>>4,i))
assert sum(map(len,rows))==272
matrix=[]
for row in rows:
    r=collections.Counter()
    for high,tag in row:r[high]+=tag
    assert sum(r.values())<=272*135
    matrix.append(r)
code=['// Exact fixed tag matrix from all 136 source links, not a sampled fit.',
 '#[inline(never)]','fn r114_tag_limb<const L:usize>(out:&mut[QM31],selectors:&Selectors){',
 '    assert!(out.len()>=30 && L<4);']
for high in sorted({h for r in matrix for h,c in r.items()if c}):
    v=f'selectors.high[{high}]';expr=f'if L==0{{{v}.c0.a.0}}else if L==1{{{v}.c0.b.0}}else if L==2{{{v}.c1.a.0}}else{{{v}.c1.b.0}}'
    code.append(f'    let h{high}=u64::from({expr});')
for i,row in enumerate(matrix):
    terms=[f'h{h}'if c==1 else f'h{h}.wrapping_mul({c})'for h,c in sorted(row.items())if c]
    expr=terms[0]+''.join(f'.wrapping_add({t})'for t in terms[1:])if terms else'0u64'
    code.append(f'    let v=M31::reduce_u64({expr});')
    code.append(f'    if L==0{{out[{i}].c0.a=v;}}else if L==1{{out[{i}].c0.b=v;}}else if L==2{{out[{i}].c1.a=v;}}else{{out[{i}].c1.b=v;}}')
code+=['}','#[inline(never)]','fn r114_tags_into(out:&mut[QM31],selectors:&Selectors){',
 '    r114_tag_limb::<0>(out,selectors);r114_tag_limb::<1>(out,selectors);r114_tag_limb::<2>(out,selectors);r114_tag_limb::<3>(out,selectors);','}']
offsets=[0]
for row in rows:offsets.append(offsets[-1]+len(row))
flat=[v for row in rows for v in row]
code+=['const _:()={',f'    let offsets:[u16;31]={offsets};',
 '    let terms:[(u8,u32);272]=['+','.join(str(v)for v in flat)+'];',
 '    let mut i=0;while i<31{assert!(offsets[i]==COPY_TAG_COORDINATE_OFFSETS[i]);i+=1;}',
 '    i=0;while i<272{assert!(terms[i].0==COPY_TAG_TERMS.0[i]);assert!(terms[i].1+R58_TAG_BASE==COPY_TAG_TERMS.1[i]);i+=1;}','};']
code+='''
#[cfg(not(v8_performance_sbf))]
pub fn r114_controls()->usize{
    let mut state=0x114eeed42119u64;let mut next=||{state^=state<<13;state^=state>>7;state^=state<<17;M31(state as u32)};
    let mut comparisons=0;
    for case in 0..1024{
        let mut high=core::array::from_fn(|_|QM31{c0:CM31::new(next(),next()),c1:CM31::new(next(),next())});
        if case<64{high.fill(QM31::ZERO);high[case]=QM31::ONE;}
        if case==64{high.fill(QM31::ZERO);}
        if case==65{let v=M31(u32::MAX);high.fill(QM31{c0:CM31::new(v,v),c1:CM31::new(v,v)});}
        let selectors=Selectors{high,low:[QM31::ONE;16]};let mut out=[QM31::ZERO;30];r114_tags_into(&mut out,&selectors);
        for i in 0..30{assert_eq!(out[i],r58_tag_delta(i,&selectors));comparisons+=1;}
    }
    comparisons
}
'''.splitlines()
save(folder/'r114_tag.rs','\n'.join(code)+'\n')
start=source.index('fn finish_selector_tensor_basis(');end=source.index('pub(crate) fn evaluate_with_selectors(',start)
body=source[start:end];needle='    let mut values = [QM31::ZERO; 4];';assert body.count(needle)==1
cfg='all(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit", feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit")'
body=body.replace(needle,f'''    #[cfg({cfg})]
    let mut r114_tags=vec![QM31::ZERO;30];
    #[cfg({cfg})]
    r114_tags_into(&mut r114_tags,selectors);
    let r114_value=|coordinate:usize|{{
        #[cfg({cfg})] {{r114_tags[coordinate]}}
        #[cfg(not({cfg}))] {{copy_tag_coordinate_value(scratch,coordinate,selectors)}}
    }};
'''+needle)
for old,new in [('copy_tag_coordinate_value(scratch, coordinate, selectors)','r114_value(coordinate)'),('copy_tag_coordinate_value(scratch, coordinate + index, selectors)','r114_value(coordinate+index)')]:
    assert body.count(old)==1;body=body.replace(old,new)
save(f,source[:start]+body+source[end:])
f=folder/'r58_tag_base.rs';save(f,f.read_text()+'\ninclude!("r114_tag.rs");\n')
f=ex/'r58_tag_check.rs';s=f.read_text();assert s.count('fn main(){')==1
save(ex/'r114_tag_check.rs',s.replace('fn main(){','fn main(){println!("R114_TAG raw_u32_coordinate_comparisons={} all_272_terms_retained=true exact_integer_matrix=true",aspis_statement::pool_v1::pair_forest_copy_terminal::r114_controls());'))
f=ex/'performance-host/Cargo.toml';save(f,f.read_text()+'\n[[bin]]\nname="r114-tag-check"\npath="../r114_tag_check.rs"\n')
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r114_native']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'protocol_changed':False,'validation_removed':False,'security_promoted':False,'new_security_claim':False,
 'fixtures':m['r105_native']['fixtures'],'changed':len(set(changed)),
 'tag_terms':272,'nonzero_matrix_terms':sum(sum(c!=0 for c in r.values())for r in matrix),'integer_matrix_checked':True}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps(m['r114_native']))
