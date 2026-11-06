from pathlib import Path
import difflib,json,hashlib
E=Path(__file__).resolve().parent;p=E/'NJL_control.rs.txt';old=p.read_text();new=old+'\n'+(E/'NJL_NATIVE_MORE.rs.txt').read_text();p.write_text(new);n='crates/aspis-statement/src/pool_v1/NJL_control.rs';(E/'NJL_MORE_WINDOWS.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+n,tofile='b/'+n)))
pins=json.loads((E/'NJL_SOURCE_PINS.json').read_text());pins[n]=hashlib.sha256(new.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(pins));p=E/'NJL_gate.py';s=p.read_text();key="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(key,"""p=S/'crates/aspis-statement/src/pool_v1/NJL_control.rs'
if 'fn NJL_recipient_actual_groups_cut' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_MORE_WINDOWS.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_MORE_WINDOWS.patch')],cwd=S,check=True)
"""+key);p.write_text(s)
names=['NJL_pattern_windows_control_cut','NJL_pattern_tail_frame_cut','NJL_pattern_forward_cut','NJL_append_group_cut','NJL_append_levels_step_cut','NJL_recipient_actual_groups_cut']
for i,name in enumerate(names):
 for negative in[False,True]:
  k=51+2*i+negative;base=50 if negative else 49;x=json.loads((E/f'NJL_K{base:03}.json').read_text());a=f'NJL_K{k:03}';x.update(attempt=a,module=name,command=['python3','NJL_gate.py',a+'.json'],expected_time='Optimized small native control/frame or ONE arbitrary-prestate arithmetic-opaque group/loop iteration; no field multiplication; SUPPORT only until full Lean root')
  x['native_command']=[v.replace('NJL_pattern_actual_map_cut',name)for v in x['native_command']];x['sources']=list(dict.fromkeys(x['sources']+['NJL_NATIVE_MORE.rs.txt']+[p.name for p in E.glob('NJL_*.patch')]));x['collect']=[v.replace(f'NJL_K{base:03}',a)for v in x['collect']];(E/(a+'.json')).write_text(json.dumps(x))
