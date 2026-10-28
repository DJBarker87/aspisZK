from pathlib import Path
import sys,importlib.util,json
E=Path(__file__).resolve().parent;sys.argv=['fix','none']
s=importlib.util.spec_from_file_location('NBN_native',E/'NBN_native.py');m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
m.admit('NBN_FEATURE_FIX');expected=json.loads((E/'NBN_ROW_SYNC.json').read_text())['lib_hash']
r=m.py(f'''from pathlib import Path
import hashlib,json
p=Path({m.B!r})/'NBN_src/crates/aspis-statement/src/lib.rs'
assert hashlib.sha256(p.read_bytes()).hexdigest()=={expected!r}
s=p.read_text();assert s.count('feature(iter_next_index)')==1
p.write_text(s.replace('feature(iter_next_index)','feature(next_index)'))
print(json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),reason='pinned compiler diagnostic identifies feature next_index; no toolchain change')))
''');assert r.returncode==0,r.stdout+r.stderr
(E/'NBN_FEATURE_FIX.json').write_text(r.stdout)
p=E/'NBN_control_rows.patch';p.write_text(p.read_text().replace('feature(iter_next_index)','feature(next_index)'))
p=E/'NBN_ROW_CUTS.json';x=json.loads(p.read_text());x['feature']='next_index in external scratch cfg(kani) only';p.write_text(json.dumps(x,indent=2)+'\n')
