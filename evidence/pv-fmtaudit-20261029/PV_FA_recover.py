"""Recover this job's receipts read-only, with a remote SHA-256 manifest."""
from pathlib import Path
import hashlib, io, json, subprocess, tarfile, sys
P = Path(__file__).parent
H = '/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029'
remote = '''from pathlib import Path
import hashlib,json,re,subprocess,time
H=Path(%r)
files=[]
for d in H.iterdir():
 if d.is_dir() and re.match(r'.*-737[0-9][0-9](?:-r[0-9]+)?$',d.name):
  files.extend(p for p in d.rglob('*')if p.is_file())
for pat in ['pincompile-artifact-*.json','resume-*.json','resume-*.tsv','resume-*.log','post-integrity.json','preflight-archive.json','preflight-resolutions*']:
 files.extend(H.glob(pat))
q=H.parent/'QUIET_WINDOW.json'
print(json.dumps(dict(time=time.time(),quiet_window=json.loads(q.read_text())if q.exists()else None,units=subprocess.getoutput('systemctl --user list-units --type=scope --all --no-pager'),processes=subprocess.getoutput('ps -eo pid,etime,args | rg "[P]V_FA_|[p]v-fmtaudit"'),files=[dict(path=str(p.relative_to(H)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)for p in sorted(set(files))])))
''' % H
r = subprocess.run(['ssh', 'dombarker@100.108.41.90', 'python3 -'],
                   input=remote, text=True, capture_output=True, check=True)
inv = json.loads(r.stdout)
(P / ('resume-recovery-' + sys.argv[1] + '.json')).write_text(json.dumps(inv, indent=1))
b = subprocess.run(['ssh', 'dombarker@100.108.41.90',
                    'tar -C ' + H + ' -cf - -- ' + ' '.join(x['path'] for x in inv['files'])],
                   capture_output=True, check=True).stdout
expected = {r['path']:r['sha256'] for r in inv['files']}
with tarfile.open(fileobj=io.BytesIO(b)) as t:
    for item in t:
        assert item.name in expected and '..' not in Path(item.name).parts
        data = t.extractfile(item).read()
        assert hashlib.sha256(data).hexdigest() == expected[item.name]
        p = P / 'host' / item.name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(data)
print('Verified and recovered', len(expected), 'files')
