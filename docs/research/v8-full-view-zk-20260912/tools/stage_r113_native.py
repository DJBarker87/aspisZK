#!/usr/bin/env python3
"""Compile common sums ACROSS Copy coordinates; not R105 within-row dedup."""
import argparse,ast,collections,hashlib,json,re,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
src=a.control;dst=a.output;here=Path(__file__).parent
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
source=(folder/'pair_forest_copy_terminal.rs').read_text();registry=(folder/'pair_forest_copy_terminal_constants.rs').read_text()
def array(name):return ast.literal_eval(re.search(r'const '+name+r':[^=]+=\s*(\[[^;]+\]);',source)[1])
group=list(zip(array('COPY_GROUP_LOCAL_COORDINATE_GROUPS'),array('COPY_GROUP_LOCAL_COORDINATE_LOCALS')))
pattern=list(zip(array('COPY_PATTERN_LOCAL_COORDINATE_GROUPS'),array('COPY_PATTERN_LOCAL_COORDINATE_PATTERNS'),array('COPY_PATTERN_LOCAL_COORDINATE_LOCALS')))
assert len(group)==len(set(group))==30 and len(pattern)==len(set(pattern))==43
link_pattern=r'CompiledPoolV1PairForestLink \{ tag: (\d+), weight_kind: (\d+), weight_level: (\d+), producer: CompiledPoolV1PairForestEndpoint \{ row: (\d+), slot: (\d+), pattern: (\d+) \}, consumer: CompiledPoolV1PairForestEndpoint \{ row: (\d+), slot: (\d+), pattern: (\d+) \} \}'
links=[list(map(int,x))for x in re.findall(link_pattern,registry)];assert len(links)==136
rows=[[]for _ in range(73)]
for i,(tag,kind,level,*ends)in enumerate(links):
    assert tag==1124073472+i and 0<=kind<=4 and 0<=level<64
    for side in range(2):
        row,slot,pat=ends[3*side:3*side+3];assert row<1024 and slot<2 and pat<14
        g=2*side+slot
        rows[group.index((g,row&15))].append((row>>4,kind,level if kind>=3 else 0))
        rows[30+pattern.index((g,pat,row&15))].append((row>>4,0,0))
assert sum(map(len,rows))==544 and all(len(x)==len(set(x))for x in rows)
keys=sorted(set(x for row in rows for x in row));targets=[set(keys.index(x)for x in row)for row in rows]
original=[s.copy()for s in targets];expansions=[collections.Counter({i:1})for i in range(len(keys))];steps=[]
while True:
    freq=collections.Counter((x,y)for s in targets for x in s for y in s if x<y)
    if not freq:break
    pair,n=max(freq.items(),key=lambda x:(x[1],-x[0][0],-x[0][1]))
    if n<2:break
    x,y=pair;idx=len(keys)+len(steps);steps.append(pair);expansions.append(expansions[x]+expansions[y])
    assert sum(expansions[-1].values())<=272
    for s in targets:
        if x in s and y in s:s.difference_update(pair);s.add(idx)
for before,after in zip(original,targets):
    expanded=collections.Counter()
    for i in after:expanded.update(expansions[i])
    assert expanded==collections.Counter({i:1 for i in before})
code=['// Generated from the pinned registry; exact integer expansion checked.',
 '// Every positive intermediate has <=272 u32 terms, hence <2^41.',
 '#[inline(never)]',
 'fn r113_limb<const L:usize>(scratch:&mut[QM31],selectors:&Selectors,append:u64,variant:PoolV1PairForestCompiledVariantV1){',
 '    assert!(scratch.len()>=103 && L<4);']
for i,(high,kind,level)in enumerate(keys):
    val=f'selectors.high[{high}]';limb=f'if L==0{{{val}.c0.a.0}}else if L==1{{{val}.c0.b.0}}else if L==2{{{val}.c1.a.0}}else{{{val}.c1.b.0}}'
    expr=f'u64::from({limb})'
    if kind:expr=f'if r57_enabled(R57Term{{high:{high},kind:{kind},level:{level}}},append,variant){{{expr}}}else{{0}}'
    code.append(f'    let v{i}={expr};')
for i,(x,y)in enumerate(steps):code.append(f'    let v{len(keys)+i}=v{x}.wrapping_add(v{y});')
for i,nodes in enumerate(targets):
    terms=sorted(nodes);expr=f'v{terms[0]}'+''.join(f'.wrapping_add(v{j})'for j in terms[1:])if terms else'0u64'
    code.append(f'    let value=M31::reduce_u64({expr});')
    code.append(f'    if L==0{{scratch[{30+i}].c0.a=value;}}else if L==1{{scratch[{30+i}].c0.b=value;}}else if L==2{{scratch[{30+i}].c1.a=value;}}else{{scratch[{30+i}].c1.b=value;}}')
code+=['}', '#[inline(never)]',
 'fn r57_gather(scratch:&mut[QM31],selectors:&Selectors,append:u64,variant:PoolV1PairForestCompiledVariantV1){',
 '    r113_limb::<0>(scratch,selectors,append,variant);r113_limb::<1>(scratch,selectors,append,variant);',
 '    r113_limb::<2>(scratch,selectors,append,variant);r113_limb::<3>(scratch,selectors,append,variant);','}']
offsets=[0]
for row in rows:offsets.append(offsets[-1]+len(row))
flat=[x for row in rows for x in row]
code+=['const _:()={',f'    let offsets:[u16;74]={offsets};',
 '    let terms:[(u8,u8,u8);544]=['+','.join(str(t)for t in flat)+'];',
 '    let mut i=0;while i<74{assert!(offsets[i]==R57_TABLE.0[i]);i+=1;}',
 '    i=0;while i<544{let t=R57_TABLE.1[i];let level=if t.kind<3{0}else{t.level};',
 '        assert!(terms[i].0==t.high && terms[i].1==t.kind && terms[i].2==level);i+=1;}','};']
new_adds=len(steps)+sum(max(0,len(s)-1)for s in targets);old_adds=sum(len(s)-1 for s in original)
code+='''
#[cfg(not(v8_performance_sbf))]
pub fn r113_controls()->usize{
    let mut state=0x113ce90223u64;let mut next=||{state^=state<<13;state^=state>>7;state^=state<<17;M31(state as u32)};
    let mut comparisons=0;
    for case in 0..1024{
        let mut high=core::array::from_fn(|_|QM31{c0:CM31::new(next(),next()),c1:CM31::new(next(),next())});
        if case<64{high.fill(QM31::ZERO);high[case]=QM31::ONE;}
        if case==64{high.fill(QM31::ZERO);}
        if case==65{let v=M31(u32::MAX);high.fill(QM31{c0:CM31::new(v,v),c1:CM31::new(v,v)});}
        let selectors=Selectors{high,low:[QM31::ONE;16]};
        let append=match case{0=>0,1=>u64::MAX,2..=65=>1u64<<(case-2),66..=129=>!(1u64<<(case-66)),_=>0x19a8beee1f456bcdu64^case as u64};
        for variant in [PoolV1PairForestCompiledVariantV1::PrivateTransfer,PoolV1PairForestCompiledVariantV1::Withdrawal]{
            let mut old=vec![QM31::ZERO;103];let mut new=vec![QM31::ZERO;103];
            r113_retained_gather(&mut old,&selectors,append,variant);r57_gather(&mut new,&selectors,append,variant);
            assert_eq!(old,new);comparisons+=1;
        }
    }
    comparisons
}
'''.splitlines()
save(folder/'r113_gather.rs','\n'.join(code)+'\n')
f=folder/'r57_selector_gather.rs';s=f.read_text();assert s.count('fn r57_gather(')==1
save(f,s.replace('fn r57_gather(','fn r113_retained_gather(')+'\ninclude!("r113_gather.rs");\n')
f=ex/'r57_selector_check.rs';s=f.read_text();assert s.count('fn main(){')==1
save(ex/'r113_copy_check.rs',s.replace('fn main(){','fn main(){println!("R113_COPY raw_u32_gather_comparisons={} exact_integer_expansion=true all_selector_basis=true",aspis_statement::pool_v1::pair_forest_copy_terminal::r113_controls());'))
f=ex/'performance-host/Cargo.toml';save(f,f.read_text()+'\n[[bin]]\nname="r113-copy-check"\npath="../r113_copy_check.rs"\n')
for f in changed:m['files'][str(f.relative_to(dst))]=sha(f)
m['r113_native']={'control':str(src),'control_manifest_sha256':sha(src/'r18-stage.json'),
 'protocol_changed':False,'validation_removed':False,'security_promoted':False,'new_security_claim':False,
 'fixtures':m['r105_native']['fixtures'],'changed':len(set(changed)),
 'unique_inputs':len(keys),'shared_nodes':len(steps),'old_additions_per_limb':old_adds,'new_additions_per_limb':new_adds,'integer_expansion_checked':True}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n')
print(json.dumps(m['r113_native']))
