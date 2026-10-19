from pathlib import Path
import json,hashlib,tarfile,io
w=Path(__file__).resolve().parent;repo=w.parent
out=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-withdrawal-success-432-20261016';out.mkdir(parents=True,exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
name='ExtractedTerminalWithdrawalSuccess';attempts=['success-a','success-b','success-c','success-d','success-e','success-f'];files={}
def add(p):
 if p.is_file() and not p.is_symlink():files[str(p.relative_to(w))]=p.read_bytes()
for label in attempts:
 for p in (w/'runs'/label).rglob('*'):add(p)
for p in [w/'runner.py',w/'success-launch-failure.json',w/'sources'/(name+'.lean'),w/'successful-targets'/(name+'.json')]:add(p)
r=json.loads((w/'successful-targets'/(name+'.json')).read_text());assert r['exit_status']==0 and r['axioms']['passed']
assert r['key']['source_sha256']==sha((w/'sources'/(name+'.lean')).read_bytes())
for suf,obj in r['objects'].items():
 p=w/'objects'/(name+suf);assert sha(p.read_bytes())==obj['sha256'];add(p)
depnames=['AspisR1TerminalValidator.Types','AspisR1TerminalValidator.FunsExternal','AspisR1TerminalValidator.Funs','ExtractedTerminalEquality']
for dep in depnames:
 add(w/'successful-targets'/(dep+'.json'));add(w/'sources'/(dep.replace('.','/')+'.lean'))
checks=''.join(f'{sha(b)}  {n}\n' for n,b in sorted(files.items())).encode();files['SHA256SUMS']=checks
archive=out/'success-sources-receipts-objects.tar.gz'
with tarfile.open(archive,'w:gz') as tf:
 for n,b in sorted(files.items()):
  info=tarfile.TarInfo(n);info.size=len(b);info.mode=0o644;info.mtime=0;tf.addfile(info,io.BytesIO(b))
closed=repo/'docs/research/100bit-spend-path-20261013/evidence/terminal-closed-cone-432-20261016/checked-sources-receipts-objects.tar.gz'
manifest={'format':1,'scope':'Actual emitted typed Withdrawal validator success implies same-public payment encoder success and every direct metadata guard; no source/runtime or nominal-carrier transport assertion.','rust_source_revision':'42e5ca2011c39ee9770afc798282ff861b092428','checked_predecessor_commit':'6315ae8fc8b5336be97fe9fb0c62c0e9067f0f8d','closed_bundle_sha256':sha(closed.read_bytes()),'archive':archive.name,'archive_sha256':sha(archive.read_bytes()),'archive_entries':len(files),'source':'docs/research/100bit-spend-path-20261013/lean/'+name+'.lean','source_sha256':r['key']['source_sha256'],'target':name,'theorem':'AspisR1TerminalValidator.TerminalWithdrawalSuccess.terminal_withdrawal_success','receipt':'successful-targets/'+name+'.json','wall_seconds':r['wall_seconds'],'peak_process_rss_kib':r['peak_process_rss_kib'],'sampled_cgroup_peak_bytes':r['sampled_cgroup_peak_bytes'],'process_swaps':r['process_swaps'],'axioms':r['axioms'],'retained_attempts':attempts,'warning':'One unused simp argument in final Err-branch proof; no checked-source cleanup rerun.','no_full_replay':True}
(out/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print(json.dumps({'entries':len(files),'bytes':archive.stat().st_size,'sha256':sha(archive.read_bytes()),'source_sha256':r['key']['source_sha256']},indent=2))
