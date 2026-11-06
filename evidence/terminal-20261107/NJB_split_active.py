from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=E/'NJB_active.rs.txt';s=p.read_text();a=s.index(' let h:[[u32;4];64]',s.index('fn NJB_active_high'));b=s.index(' let k:usize=',a)
s=s[:a]+''' // Selectors and QM31 contain only integer fields; every bit-pattern is valid.
 let selectors:Selectors=unsafe{kani::any_raw()};let mut sums:[QM31;7]=unsafe{kani::any_raw()};let hs=sums;let b:usize=kani::any();kani::assume(b<64);
 let c=match constants::ACTIVE_ROW_MASKS[b]{6144=>0,6145=>1,4097=>2,2048=>3,2049=>4,26214=>5,1749=>6,_=>unreachable!()};
 let reply:[u32;4]=kani::any();kani::assume(canon(words(hs[c]))&&canon(words(selectors.high[b]))&&canon(reply));let mut r=[[0;4];17];r[0]=reply;
 let mut log=NJB_Log{left:[[0;4];17],right:[[0;4];17],reply:r,kind:[0;17],calls:0};let next=NJB_high_step(&selectors,&mut sums,b,&mut log);
'''+s[b:]
s=s.replace('hs[c][limb]','words(hs[c])[limb]').replace('h[b][limb]','words(selectors.high[b])[limb]').replace('else{hs[k][limb]}','else{words(hs[k])[limb]}')
# Low target has not run yet: same native step, direct arbitrary valid integer records.
a=s.index(' let h:[[u32;4];64]',s.index('fn NJB_active_low'));b=s.index(' let counts=',a)
s=s[:a]+''' // Every field is a u32 under transparent integer wrappers; no enum/pointer validity constraint.
 let selectors:Selectors=unsafe{kani::any_raw()};let high_sums:[QM31;7]=unsafe{kani::any_raw()};let hs=high_sums.map(words);let lo=selectors.low.map(words);let r:[[u32;4];17]=kani::any();let sum:[u32;4]=kani::any();assume_all(lo);assume_all(hs);assume_all(r);kani::assume(canon(sum));
 let c:usize=kani::any();kani::assume(c<7);let mut log=NJB_Log{left:[[0;4];17],right:[[0;4];17],reply:r,kind:[0;17],calls:0};let (out,next)=NJB_low_step(&selectors,&high_sums,q(sum),c,&mut log);
'''+s[b:]
p.write_text(s)
(E/'NJB_update_active.py').write_text('''from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent;s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());q='crates/aspis-statement/src/pool_v1/NJB_active.rs';p=s/q;assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q];raw=(b/'NJB_active.rs.txt').read_bytes();p.write_bytes(raw);pins[q]=hashlib.sha256(raw).hexdigest();(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('active harness initialization split; native step name/body unchanged')
''')
x=dict(attempt='NJB_L018',kind='setup',module='NJB_active_initialization_split',sources=['NJB_update_active.py','NJB_active.rs.txt'],command=['python3','NJB_update_active.py'],timeout=180,env={'CARGO_TARGET_DIR':'/home/dombarker/project-offloads/codex-cx-terminal-20261107/NJB_target'},deps_fingerprint={},collect=['NJB_SOURCE_PINS.json'],expected_time='Replace harness construction loops with direct arbitrary valid integer records after high-step timeout; same target/name/assertions')
(E/'NJB_L018.json').write_text(json.dumps(x))
for i,src in [(12,8),(13,9)]:
 x=json.loads((E/f'NJB_K{src:03}.json').read_text());a=f'NJB_K{i:03}';old=x['attempt'];x['attempt']=a;x['command'][-1]=a+'.json';x['collect']=[p.replace(old,a)for p in x['collect']];(E/(a+'.json')).write_text(json.dumps(x))
print('high-step timeout isolated to initialization/memory shape; direct arbitrary pre-state replacement prepared')
