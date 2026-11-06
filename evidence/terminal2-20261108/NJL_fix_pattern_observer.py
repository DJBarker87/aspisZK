from pathlib import Path
import difflib,json,hashlib,subprocess
E=Path(__file__).resolve().parent;n='crates/aspis-core/src/field.rs';oldfield=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True);suffix='\n#[cfg(kani)]\n#[path="NJL_observe.rs"]\npub mod NJL_observe;\n';newfield=oldfield+suffix
observe=(E.parent/'terminal-20261107/NJB_observe.rs.txt').read_text();(E/'NJL_observe.rs.txt').write_text(observe)
p=E/'NJL_control.rs.txt';old=p.read_text();new=old.replace('aspis_core::field::NJB_observe','aspis_core::field::NJL_observe');assert new!=old;p.write_text(new);m='crates/aspis-statement/src/pool_v1/NJL_control.rs'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+m,tofile='b/'+m))+''.join(difflib.unified_diff(oldfield.splitlines(True),newfield.splitlines(True),fromfile='a/'+n,tofile='b/'+n))+''.join(difflib.unified_diff([],observe.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-core/src/NJL_observe.rs'))
(E/'NJL_PATTERN_OBSERVER.patch').write_text(patch);pins=json.loads((E/'NJL_SOURCE_PINS.json').read_text());pins[m]=hashlib.sha256(new.encode()).hexdigest();pins[n]=hashlib.sha256(newfield.encode()).hexdigest();pins['crates/aspis-core/src/NJL_observe.rs']=hashlib.sha256(observe.encode()).hexdigest();(E/'NJL_SOURCE_PINS.json').write_text(json.dumps(pins))
p=E/'NJL_gate.py';s=p.read_text();key="frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'";s=s.replace(key,f'''p=S/'crates/aspis-core/src/field.rs'
if 'pub mod NJL_observe' not in p.read_text():
 subprocess.run(['git','apply','--check',str(B/'NJL_PATTERN_OBSERVER.patch')],cwd=S,check=True)
 subprocess.run(['git','apply',str(B/'NJL_PATTERN_OBSERVER.patch')],cwd=S,check=True)
suffix={suffix!r}.encode();field=p.read_bytes();assert field.endswith(suffix)
assert hashlib.sha256(field[:-len(suffix)]).hexdigest()=={hashlib.sha256(oldfield.encode()).hexdigest()!r},'STOP non-harness field body changed'
'''+key);p.write_text(s)
for k,base in[(49,45),(50,46),(47,47),(48,48)]:
 x=json.loads((E/f'NJL_K{base:03}.json').read_text());a=f'NJL_K{k:03}';x.update(attempt=a,command=['python3','NJL_gate.py',a+'.json'])
 x['sources']=list(dict.fromkeys(x['sources']+['NJL_observe.rs.txt']+[p.name for p in E.glob('NJL_*.patch')]));x['collect']=[v.replace(f'NJL_K{base:03}',a)for v in x['collect']];(E/(a+'.json')).write_text(json.dumps(x))
(E/'NJL_OBSERVER_PROVENANCE.json').write_text(json.dumps(dict(source='evidence/terminal-20261107/NJB_observe.rs.txt',sha256=hashlib.sha256(observe.encode()).hexdigest(),change='Exact predecessor field observer reused under OWN cfg(kani)-only module name; frozen field.rs prefix is independently hash-checked before EVERY run',frozen_field_sha256=hashlib.sha256(oldfield.encode()).hexdigest(),shipped='No repository crates/programs change; scratch only; no production arithmetic edits'),indent=2)+'\n')
with(E/'NJL_FIXES.md').open('a')as f:f.write('\nK045 failed before verification because NJB_observe is not in the own frozen scratch. K046 not run. Copied exact predecessor9word observer into OWN NJL_observe cfg(kani)-only scratch module, with independent frozen field-prefix hash validation on every run. K049/K050 reestablish actual map, same harness/assertions; no verdict bypass.\n')
