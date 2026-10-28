from pathlib import Path
import sys,importlib.util,json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;sys.argv=['split','none']
s=importlib.util.spec_from_file_location('NBN_native',E/'NBN_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
# Solver scratch is exclusive to this job and the timed-out solver is terminal.
r=m.py(f'''from pathlib import Path
import json
p=Path({m.B!r})/'NBN_tmp';removed=[]
for f in p.rglob('*'):
 if f.is_file() and (f.name.startswith('external-sat') or f.name.startswith('smt2_dec_problem')):
  removed.append(dict(path=str(f),bytes=f.stat().st_size));f.unlink()
print(json.dumps(dict(removed=removed,total_bytes=sum(f['bytes'] for f in removed))))
''');assert r.returncode==0,r.stdout+r.stderr
(E/'NBN_K007_CLEANUP.json').write_text(r.stdout)
p=E/'NBN_more.rs.txt';old=p.read_text();extra='''
// Library-copy boundary after the separately checked native slice range/pointer cut.
#[kani::proof]
#[kani::unwind(1881)]
fn NBN_copy32_boundary(){
 let mut out:[u8;32]=kani::any();let bytes:[u8;32]=kani::any();
 let j:usize=kani::any();kani::assume(j<32);
 out.copy_from_slice(&bytes);assert_eq!(out[j],bytes[j]);
}
''';assert 'fn NBN_copy32_boundary' not in old;new=old+extra;p.write_text(new)
m.admit('NBN_COPY_SPLIT_SYNC')
r=m.py(f'''from pathlib import Path
import hashlib,json
p=Path({m.B!r})/'NBN_src/crates/aspis-statement/src/pool_v1/NBN_more.rs'
assert hashlib.sha256(p.read_bytes()).hexdigest()=={hashlib.sha256(old.encode()).hexdigest()!r}
p.write_text({new!r});print(json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest())))
''');assert r.returncode==0,r.stdout+r.stderr
(E/'NBN_COPY_SPLIT_SYNC.json').write_text(r.stdout)
base='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';b=subprocess.check_output(['git','show',m.REV+':'+base],text=True);inc='\n#[cfg(kani)]\n#[path="NBN_more.rs"]\nmod NBN_more;\n'
lib='crates/aspis-statement/src/lib.rs';l=subprocess.check_output(['git','show',m.REV+':'+lib],text=True);attr='#![cfg_attr(kani, feature(next_index))]\n'
patch=''.join(difflib.unified_diff(b.splitlines(True),(b+inc).splitlines(True),fromfile='a/'+base,tofile='b/'+base))
patch+=''.join(difflib.unified_diff(l.splitlines(True),(attr+l).splitlines(True),fromfile='a/'+lib,tofile='b/'+lib))
patch+=''.join(difflib.unified_diff([],new.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-statement/src/pool_v1/NBN_more.rs'))
(E/'NBN_control_split.patch').write_text(patch)
