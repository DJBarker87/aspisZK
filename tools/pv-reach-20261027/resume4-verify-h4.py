import subprocess,json,pathlib,hashlib,shlex
root=pathlib.Path(__file__).resolve().parents[2]; e=root/'evidence/pv-reach-20261027/resume4'
p=e/'external-object-manifest.json'; rows=json.loads(p.read_text())
script='''import json,hashlib,pathlib,sys
rows=json.load(sys.stdin);out=[]
for r in rows:
 p=pathlib.Path(r['path']);h=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
 out.append(dict(module=r['module'],path=str(p),expected=r['object_sha256'],actual=h,match=h==r['object_sha256']))
print(json.dumps(out))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],input=p.read_text(),text=True,capture_output=True,check=True)
out=json.loads(r.stdout); report=dict(authority='research:evidence/pv-replay-20261027/receipts/external-object-manifest.json',manifest_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),verified_before_first_resume4_compile=True,objects=len(out),mismatches=[x for x in out if not x['match']],checks=out)
(e/'h4-verification.json').write_text(json.dumps(report,indent=2)+'\n');print('objects',len(out),'mismatches',len(report['mismatches']));assert not report['mismatches']
