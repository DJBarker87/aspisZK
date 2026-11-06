from pathlib import Path
import difflib,json,hashlib
E=Path(__file__).resolve().parent;p=E/'NJL_control.rs.txt';old=p.read_text();needle='assert_eq!(l.index,index);assert_eq!(l.level,level);';replacement='assert_eq!(l.index,index ^ if cfg!(NJL_wrong_index){1}else{0});assert_eq!(l.level,level);';assert old.count(needle)==1;new=old.replace(needle,replacement);p.write_text(new);n='crates/aspis-statement/src/pool_v1/NJL_control.rs';(E/'NJL_U64_CONTROL.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
pins=json.loads((E/'NJL_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(new.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(pins));p=E/'NJL_gate.py';s=p.read_text();key="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(key,"""p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'cfg!(NJL_wrong_index)' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_U64_CONTROL.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_U64_CONTROL.patch')],cwd=S,check=True)
"""+key);p.write_text(s)
x=json.loads((E/'NJL_K060.json').read_text().replace('NJL_invert','NJL_wrong_index'));a='NJL_K063';x.update(attempt=a,command=['python3','NJL_gate.py',a+'.json'],expected_time='Additional failing fidelity control ONLY: corrupt observed forwarded u64 index while normal output/frame checks remain unchanged; no new positive/root credit')
x['sources']=list(dict.fromkeys(x['sources']+[p.name for p in E.glob('NJL_*.patch')]));x['collect']=[v.replace('NJL_K060',a)for v in x['collect']];(E/(a+'.json')).write_text(json.dumps(x))
(E/'NJL_U64_CONTROL.json').write_text(json.dumps(dict(purpose='Independently test non-copy u64 argument forwarding rather than only output-copy failure',harness='NJL_append_levels_step_cut',positive_property='l.index == index, already checked by K059',inverted_property='l.index == (index XOR1)',expected='FAIL',credit='None added: K059/K060 remain the retained original same-source pair for SUPPORT235; K063 is an extra negative fidelity observation, never a passing bridge'),indent=2)+'\n')
