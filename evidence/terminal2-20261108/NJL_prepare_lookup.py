from pathlib import Path
import re,json,subprocess,hashlib,difflib
E=Path(__file__).resolve().parent;source=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs']).decode()
def nums(name):
 a=re.search(r'const '+name+r':\s*\[u8;\s*\d+\]\s*=\s*\[([^]]+)\]',source,re.S);assert a,name
 return [int(t)for t in re.findall(r'\d+',a[1])]
groups=list(zip(nums('COPY_GROUP_LOCAL_COORDINATE_GROUPS'),nums('COPY_GROUP_LOCAL_COORDINATE_LOCALS')));patterns=list(zip(nums('COPY_PATTERN_LOCAL_COORDINATE_GROUPS'),nums('COPY_PATTERN_LOCAL_COORDINATE_PATTERNS'),nums('COPY_PATTERN_LOCAL_COORDINATE_LOCALS')));assert len(groups)==len(set(groups))==30 and len(patterns)==len(set(patterns))==43
(E/'NJL_LOOKUP_TABLE.json').write_text(json.dumps(dict(source_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',source_sha256=hashlib.sha256(source.encode()).hexdigest(),group_keys=groups,pattern_keys=patterns,unique=True,native_model='first matching source key index; absent255; native builder writes each unique key exactly once'),indent=2))
rust='\nconst NJL_GROUP_KEYS:[(usize,usize);30]=['+','.join('('+','.join(map(str,k))+')'for k in groups)+'];\n'
rust+='const NJL_PATTERN_KEYS:[(usize,usize,usize);43]=['+','.join('('+','.join(map(str,k))+')'for k in patterns)+'];\n'
rust+='''fn NJL_group_model(g:usize,l:usize)->usize{let mut i=0;while i<30{if NJL_GROUP_KEYS[i]==(g,l){return i;}i+=1;}255}
fn NJL_pattern_model(g:usize,p:usize,l:usize)->usize{let mut i=0;while i<43{if NJL_PATTERN_KEYS[i]==(g,p,l){return i;}i+=1;}255}
fn NJL_endpoint_lookup(selectors:&Selectors,index:usize,consumer:bool)->(usize,usize,usize,QM31){
 let link=constants::COPY_LINKS[index];let(side,endpoint)=if consumer{(2,link.consumer)}else{(0,link.producer)};
 let group=side+usize::from(endpoint.slot);let row=usize::from(endpoint.row);let local=row&15;
 let high=selectors.high[row>>4];let gc=usize::from(COPY_GROUP_LOCAL_COORDINATES[group][local]);
 let pc=usize::from(COPY_PATTERN_LOCAL_COORDINATES[group][usize::from(endpoint.pattern)][local]);
 (row,gc,pc,high)
}
#[kani::proof] #[kani::unwind(145)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJL_endpoint_lookup_cut(){
 let selectors:Selectors=unsafe{core::mem::transmute::<[[u32;4];80],Selectors>(kani::any())};
 let index:usize=kani::any();let consumer:bool=kani::any();let limb:usize=kani::any();kani::assume(index<136&&limb<4);
 let(row,gc,pc,high)=NJL_endpoint_lookup(&selectors,index,consumer);
 let link=constants::COPY_LINKS[index];let e=if consumer{link.consumer}else{link.producer};
 let group=(if consumer{2}else{0})+usize::from(e.slot);let local=usize::from(e.row)&15;
 assert!(row<1024&&gc<30&&pc<43);assert_eq!(row,usize::from(e.row));
 assert_eq!(gc,NJL_group_model(group,local)+if cfg!(NJL_invert){1}else{0});
 assert_eq!(pc,NJL_pattern_model(group,usize::from(e.pattern),local));
 assert_eq!(NJL_words(high)[limb],NJL_words(selectors.high[row>>4])[limb]);
}
'''
p=E/'NJL_control.rs.txt';old=p.read_text();new=old+rust;p.write_text(new);n='crates/aspis-statement/src/pool_v1/NJL_control.rs';(E/'NJL_LOOKUP_WINDOW.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)));pins=json.loads((E/'NJL_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(new.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(pins));p=E/'NJL_gate.py';s=p.read_text();key="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(key,"""p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_endpoint_lookup_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_LOOKUP_WINDOW.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_LOOKUP_WINDOW.patch')],cwd=S,check=True)
"""+key);p.write_text(s)
for k in [13,14]:
 x=json.loads((E/'NJL_K012.json').read_text());a=f'NJL_K{k:03}';x.update(attempt=a,module='NJL_endpoint_lookup_cut',command=['python3','NJL_gate.py',a+'.json'],expected_time='Optimized genuine136-link/two-side native lookup against source-key scan model, scalar selected-high window; no arithmetic, new missing table/argument binding')
 x['native_command']=[v.replace('NJL_endpoint_write_cut','NJL_endpoint_lookup_cut')for v in x['native_command']];x['sources']+=['NJL_LOOKUP_WINDOW.patch','NJL_LOOKUP_TABLE.json'];x['collect']=[v.replace('NJL_K012',a)for v in x['collect']];x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NJL_invert'if k==14 else'');(E/(a+'.json')).write_text(json.dumps(x))
print('Source-key scan versus frozen inverse-table lookup prepared, all136links/bothsides')
