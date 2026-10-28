from pathlib import Path
import json,subprocess,importlib.util,sys
E=Path(__file__).resolve().parent
sys.argv=['sync','none'];spec=importlib.util.spec_from_file_location('NBK_native',E/'NBK_native.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
m.admit('NBK_SYNC_MORE')
parent='crates/aspis-statement/src/pool_v1/pair_terminal.rs'
original=subprocess.check_output(['git','show',m.REV+':'+parent],text=True)
marker='\n#[cfg(kani)]\n#[path="NBK_codecs.rs"]\nmod NBK_codecs;\n'
more='\n#[cfg(kani)]\n#[path="NBK_more.rs"]\nmod NBK_more;\n'
payload={'original':original,'marker':marker,'more':more,'source':(E/'NBK_more.rs.txt').read_text()}
(E/'NBK_SYNC_MORE-payload.json').write_text(json.dumps(payload,indent=2)+'\n')
r=m.py(f'''from pathlib import Path
import json,hashlib
b=Path({m.B!r})/'NBK_src';x=json.loads({json.dumps(json.dumps(payload))});p=b/{parent!r}
assert p.read_text()==x['original']+x['marker'],'Unexpected scratch parent'
p.write_text(x['original']+x['marker']+x['more']);q=p.parent/'NBK_more.rs';assert not q.exists();q.write_text(x['source'])
print(json.dumps({{str(p):hashlib.sha256(p.read_bytes()).hexdigest(),str(q):hashlib.sha256(q.read_bytes()).hexdigest()}},indent=2))
''',submitted=True)
(E/'NBK_SYNC_MORE-transport.json').write_text(json.dumps({'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'submitted_once':True},indent=2)+'\n')
assert r.returncode==0,'STOP/recover read-only; do not repeat sync submission'
# Future Kani source manifests must include the new module.
p=E/'NBK_native.py';s=p.read_text();s=s.replace("'NBK_src/crates/aspis-statement/src/pool_v1/NBK_codecs.rs']","'NBK_src/crates/aspis-statement/src/pool_v1/NBK_codecs.rs','NBK_src/crates/aspis-statement/src/pool_v1/NBK_more.rs']");p.write_text(s)
(E/'NBK_harness_stores.patch').write_bytes((E/'NBK_harness.patch').read_bytes());(E/'NBK_harness.patch').write_bytes((E/'NBK_harness_next.patch').read_bytes())
