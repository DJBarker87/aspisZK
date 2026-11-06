from pathlib import Path
import difflib,json,hashlib
E=Path(__file__).resolve().parent;p=E/'NJL_control.rs.txt';old=p.read_text();new=old.replace('StateOnlyPoseidonOpeningsas usize','StateOnlyPoseidonOpenings as usize');assert new!=old;p.write_text(new);n='crates/aspis-statement/src/pool_v1/NJL_control.rs';(E/'NJL_PATH_TYPE_FIX.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
pins=json.loads((E/'NJL_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(new.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(pins));p=E/'NJL_gate.py';s=p.read_text();key="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(key,"""p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'StateOnlyPoseidonOpeningsas usize' in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_PATH_TYPE_FIX.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_PATH_TYPE_FIX.patch')],cwd=S,check=True)
"""+key);p.write_text(s)
for k,base in[(43,41),(44,42)]:
 x=json.loads((E/f'NJL_K{base:03}.json').read_text());a=f'NJL_K{k:03}';x.update(attempt=a,command=['python3','NJL_gate.py',a+'.json'])
 x['sources']=list(dict.fromkeys(x['sources']+[p.name for p in E.glob('NJL_*.patch')]));x['collect']=[v.replace(f'NJL_K{base:03}',a)for v in x['collect']];(E/(a+'.json')).write_text(json.dumps(x))
with(E/'NJL_FIXES.md').open('a')as f:f.write('\nK041 failed Rust parsing before verification: missing whitespace in `StateOnlyPoseidonOpenings as usize` generated replacement. K042 not run. Fix exactly whitespace; replacement K043/K044 same assertions and original harness name; no verdict bypass.\n')
