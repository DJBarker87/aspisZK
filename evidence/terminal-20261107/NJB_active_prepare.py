from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent;q='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';src=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+q]).decode();a=src.index('fn active_mask_basis(');b=src.index('while block <',a)
def braced(s,start):
 op=s.index('{',start);d=1;i=op+1
 while d:d+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[op+1:i-1],i
body,end=braced(src,b);body2,end2=braced(src,src.index('while coordinate <',end))
def logs(s):
 insert={}
 for m in re.finditer(r'\.(mul|add|sub)\(',s):
  j=m.end();d=1
  while d:d+=(s[j]=='(')-(s[j]==')');j+=1
  insert[j-1]=',log'+insert.get(j-1,'');insert[m.start()+1]='NJB_'+insert.get(m.start()+1,'')
 for i,t in sorted(insert.items(),reverse=True):s=s[:i]+t+s[i:]
 return s.replace('self.','selectors.')
helper=(E/'NJB_residual.rs.txt').read_text().split('fn NJB_copy_residual')[0]
first='fn NJB_high_step(selectors:&Selectors,high_sums:&mut [QM31;7],mut block:usize,log:&mut NJB_Log)->usize{'+logs(body)+'block}'
second='fn NJB_low_step(selectors:&Selectors,high_sums:&[QM31;7],mut sum:QM31,mut coordinate:usize,log:&mut NJB_Log)->(QM31,usize){'+logs(body2)+'(sum,coordinate)}'
# The two bodies erase exactly, modulo self -> selectors binding and product logging.
for orig,new in [(body,logs(body)),(body2,logs(body2))]:assert new.replace('.NJB_','.').replace(',log','').replace('selectors.','self.')==orig
h='''
fn assume_all<const N:usize>(a:[[u32;4];N]){for w in a{kani::assume(canon(w));}}
#[kani::proof]#[kani::unwind(82)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_active_high(){
 let h:[[u32;4];64]=kani::any();let lo:[[u32;4];16]=kani::any();let hs:[[u32;4];7]=kani::any();let r:[[u32;4];17]=kani::any();assume_all(h);assume_all(lo);assume_all(hs);assume_all(r);
 let selectors=Selectors{high:h.map(q),low:lo.map(q)};let mut sums=hs.map(q);let b:usize=kani::any();kani::assume(b<64);
 let c=match constants::ACTIVE_ROW_MASKS[b]{6144=>0,6145=>1,4097=>2,2048=>3,2049=>4,26214=>5,1749=>6,_=>unreachable!()};
 let mut log=NJB_Log{left:[[0;4];17],right:[[0;4];17],reply:r,kind:[0;17],calls:0};let next=NJB_high_step(&selectors,&mut sums,b,&mut log);
 let k:usize=kani::any();let limb:usize=kani::any();kani::assume(k<7&&limb<4);
 assert_eq!(next,b+1);assert_eq!(log.calls,1);assert_eq!(log.kind[0],1);assert_eq!(log.left[0][limb],hs[c][limb]);assert_eq!(log.right[0][limb],h[b][limb]);
 assert_eq!(words(sums[k])[limb],(if k==c{r[0][limb]}else{hs[k][limb]}) ^ if cfg!(NJB_invert){1}else{0});
}
#[kani::proof]#[kani::unwind(82)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJB_active_low(){
 let h:[[u32;4];64]=kani::any();let lo:[[u32;4];16]=kani::any();let hs:[[u32;4];7]=kani::any();let r:[[u32;4];17]=kani::any();let sum:[u32;4]=kani::any();assume_all(h);assume_all(lo);assume_all(hs);assume_all(r);kani::assume(canon(sum));
 let selectors=Selectors{high:h.map(q),low:lo.map(q)};let c:usize=kani::any();kani::assume(c<7);let mut log=NJB_Log{left:[[0;4];17],right:[[0;4];17],reply:r,kind:[0;17],calls:0};let (out,next)=NJB_low_step(&selectors,&hs.map(q),q(sum),c,&mut log);
 let counts=[2,3,2,1,2,8,7];let indices=[[11,12,0,0,0,0,0,0],[0,11,12,0,0,0,0,0],[0,12,0,0,0,0,0,0],[11,0,0,0,0,0,0,0],[0,11,0,0,0,0,0,0],[1,2,5,6,9,10,13,14],[0,2,4,6,7,9,10,0]];let n=counts[c];let j:usize=kani::any();let limb:usize=kani::any();kani::assume(j<n+1&&limb<4);
 let left=if j<n-1{if j==0{lo[indices[c][0]]}else{r[j-1]}}else if j==n-1{hs[c]}else{sum};
 let right=if j<n-1{lo[indices[c][j+1]]}else if j==n-1{if n==1{lo[indices[c][0]]}else{r[n-2]}}else{r[n-1]};
 assert_eq!(next,c+1);assert_eq!(log.calls,n+1);assert_eq!(words(out)[limb],r[n][limb]);assert_eq!(log.kind[j],if j==n-1{0}else{1});assert_eq!(log.left[j][limb],left[limb] ^ if cfg!(NJB_invert){1}else{0});assert_eq!(log.right[j][limb],right[limb]);
}
'''
(E/'NJB_active.rs.txt').write_text(helper+first+'\n'+second+h)
(E/'NJB_ACTIVE_ERASURE.json').write_text(json.dumps(dict(source=q,high_body=body,low_body=body2,high_sha256=hashlib.sha256(body.encode()).hexdigest(),low_sha256=hashlib.sha256(body2.encode()).hexdigest(),erasure_equal=True),indent=1))
(E/'NJB_install_active.py').write_text('''from pathlib import Path
import json,hashlib
b=Path(__file__).resolve().parent;s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());q='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';p=s/q;assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[q];p.write_text(p.read_text()+'\\n#[cfg(kani)]\\n#[path="NJB_active.rs"]\\nmod NJB_active_native;\\n');pins[q]=hashlib.sha256(p.read_bytes()).hexdigest();q='crates/aspis-statement/src/pool_v1/NJB_active.rs';(s/q).write_bytes((b/'NJB_active.rs.txt').read_bytes());pins[q]=hashlib.sha256((s/q).read_bytes()).hexdigest();(b/'NJB_SOURCE_PINS.json').write_text(json.dumps(pins));print('two arbitrary-prestate active-mask native loop steps installed')
''')
x=dict(attempt='NJB_L014',kind='setup',module='NJB_active_install',sources=['NJB_install_active.py','NJB_active.rs.txt','NJB_ACTIVE_ERASURE.json'],command=['python3','NJB_install_active.py'],timeout=180,env={'CARGO_TARGET_DIR':'/home/dombarker/project-offloads/codex-cx-terminal-20261107/NJB_target'},deps_fingerprint={},collect=['NJB_SOURCE_PINS.json'],expected_time='Install two native iteration cuts, no whole-buffer loop')
(E/'NJB_L014.json').write_text(json.dumps(x))
for i in range(8,12):
 x=json.loads((E/'NJB_K006.json').read_text());a=f'NJB_K{i:03}';which='high'if i<10 else'low';x['attempt']=a;x['module']='NJB_active_'+which;x['command'][-1]=a+'.json';x['sources']+=['NJB_active.rs.txt','NJB_ACTIVE_ERASURE.json'];x['native_command']=[v.replace('pool_v1::pair_forest_copy_terminal::NJB_native::NJB_residual','pool_v1::pair_forest_copy_terminal::NJB_active_native::NJB_active_'+which)for v in x['native_command']];x['collect']=[p.replace('NJB_K006',a)for p in x['collect']];x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NJB_invert'if i%2 else'');x['expected_time']='Optimized one-iteration '+which+' local-record cut; all field products opaque';(E/(a+'.json')).write_text(json.dumps(x))
print('active-mask two native iterations prepared; exact body erasures recorded')
