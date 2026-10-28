from pathlib import Path
import sys,json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBM_host as h
r=h.remote_py(f'''from pathlib import Path
import json,hashlib
b=Path({h.B!r});out={{}}
for name in ['NBM_R001-graph.json','NBM_R001-metadata.stderr']:
 p=b/name
 if p.exists():out[name]=p.read_text()
print(json.dumps(out))''');assert r.returncode==0,r.stderr
for name,s in json.loads(r.stdout).items():(E/name).write_text(s)
# Exact patch is limited to the scratch-only module hook and its test.
R=E.parents[1];f='crates/aspis-r1-cost-probe/src/multiproof.rs';base=(R/f).read_text();hook=base+'\n#[cfg(kani)]\n#[path = \"NBM_copy.rs\"]\nmod NBM_copy;\n'
patch=''.join(difflib.unified_diff(base.splitlines(True),hook.splitlines(True),fromfile='a/'+f,tofile='b/'+f))
f2='crates/aspis-r1-cost-probe/src/NBM_copy.rs';s=(E/'NBM_copy.rs.txt').read_text()
patch+=''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/'+f2))
(E/'NBM_playback.patch').write_text(patch)
old=(R/'evidence/native-tx1c-20261027/NBJ_K050/stdout.log').read_text().split('```')[1].strip()
assert old in s
(E/'NBM_PLAYBACK_IDENTITY.json').write_text(json.dumps(dict(generated_test_sha256=hashlib.sha256(old.encode()).hexdigest(),verbatim_test_retained=True,generated_test_origin='evidence/native-tx1c-20261027/NBJ_K050/stdout.log',prior_harness='NBJ_count_copy_prefix',only_module_renamed='multiproof::NBM_copy',input_words=[0]*7+[1]+[0]*7+[512],n=16,k=15),indent=2)+'\n')
