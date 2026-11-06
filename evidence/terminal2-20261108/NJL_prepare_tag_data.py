from pathlib import Path
import re,json,subprocess,hashlib,difflib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';src=subprocess.check_output(['git','show',rev+':crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs']).decode();keys=json.loads((E/'NJL_LOOKUP_TABLE.json').read_text())['group_keys'];gc={tuple(k):i for i,k in enumerate(keys)}
links=[]
for line in src.splitlines():
 if 'CompiledPoolV1PairForestLink { tag:' not in line:continue
 tag=int(re.search(r'tag:\s*(\d+)',line)[1]);ep=[tuple(map(int,m))for m in re.findall(r'Endpoint\s*\{\s*row:\s*(\d+),\s*slot:\s*(\d+),\s*pattern:\s*(\d+)\s*\}',line)];assert len(ep)==2;links.append((tag,ep))
assert len(links)==136;coords=[[]for _ in range(30)]
for i,(tag,endpoints)in enumerate(links):
 for side,(row,slot,pattern)in enumerate(endpoints):
  c=gc[(side*2+slot,row&15)];coords[c].append(dict(block=row>>4,tag=tag,link=i,consumer=bool(side)))
offsets=[0]
for terms in coords:offsets.append(offsets[-1]+len(terms))
terms=[t for c in coords for t in c];assert len(terms)==272 and all(t['block']<64 and t['tag']<2147483647 for t in terms)
x=dict(revision=rev,source_sha256=hashlib.sha256(src.encode()).hexdigest(),offsets=offsets,terms=terms,spans=[len(c)for c in coords],min_span=min(map(len,coords)),max_span=max(map(len,coords)),empty_coordinates=[i for i,c in enumerate(coords)if not c]);(E/'NJL_TAG_DATA.json').write_text(json.dumps(x,indent=1)+'\n')
rust='\nconst NJL_TAG_OFFSETS:[usize;31]=['+','.join(map(str,offsets))+'];\n'
rust+='const NJL_TAG_BLOCKS:[u8;272]=['+','.join(str(t['block'])for t in terms)+'];\n'
rust+='const NJL_TAG_WEIGHTS:[u32;272]=['+','.join(str(t['tag'])for t in terms)+'];\n'
rust+='''#[kani::proof] #[kani::unwind(4)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NJL_tag_registry_cut(){
 let index:usize=kani::any();let coordinate:usize=kani::any();kani::assume(index<272&&coordinate<30);
 let block=COPY_TAG_TERMS.0[index];let tag=COPY_TAG_TERMS.1[index];
 let start=usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate]);let end=usize::from(COPY_TAG_COORDINATE_OFFSETS[coordinate+1]);
 assert!(block<64&&tag<2147483647&&start<=end&&end<=272);
 assert_eq!(block,NJL_TAG_BLOCKS[index] ^ if cfg!(NJL_invert){1}else{0});
 assert_eq!(tag,NJL_TAG_WEIGHTS[index]);assert_eq!(start,NJL_TAG_OFFSETS[coordinate]);assert_eq!(end,NJL_TAG_OFFSETS[coordinate+1]);
}
'''
p=E/'NJL_control.rs.txt';old=p.read_text();new=old+rust;p.write_text(new);n='crates/aspis-statement/src/pool_v1/NJL_control.rs';(E/'NJL_TAG_REGISTRY.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)));pins=json.loads((E/'NJL_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(new.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(pins));p=E/'NJL_gate.py';s=p.read_text();key="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(key,"""p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_tag_registry_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_TAG_REGISTRY.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_TAG_REGISTRY.patch')],cwd=S,check=True)
"""+key);p.write_text(s)
for k,base in [(21,19),(22,20)]:
 y=json.loads((E/f'NJL_K{base:03}.json').read_text());a=f'NJL_K{k:03}';y.update(attempt=a,module='NJL_tag_registry_cut',command=['python3','NJL_gate.py',a+'.json'],expected_time='Optimized frozen272term/31offset registry against exact literal model data; no arithmetic, no new extracted reference')
 y['native_command']=[v.replace('NJL_endpoint_lookup_cut','NJL_tag_registry_cut')for v in y['native_command']];y['sources']+=['NJL_TAG_REGISTRY.patch','NJL_TAG_DATA.json'];y['collect']=[v.replace(f'NJL_K{base:03}',a)for v in y['collect']];(E/(a+'.json')).write_text(json.dumps(y))
print(json.dumps({k:x[k]for k in ['min_span','max_span','empty_coordinates','spans']}))
