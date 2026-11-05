from pathlib import Path
import hashlib,json,lzma,subprocess,runpy
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
J=lambda n:json.loads((E/n).read_bytes())
if __name__=='__main__':
 ctx=runpy.run_path(str(E/'NHH_validate.py'),run_name='NHH_static_validation')
 assert ctx['gate'](*[J(n)for n in ['NHH_CLOSED.json','NHH_LEDGER_DELTA.json','NHH_EDGES.json','NHH_AUDIT.json','NHH_NATIVE_VALIDATION.json','NHH_SOURCE_VALIDATION.json']])
 compressed=[]
 for p in E.rglob('*.xz'):
  side=p.with_suffix(p.suffix+'.sha256')
  if not side.exists():side=p.with_suffix('.sha256')
  assert side.exists(),p
  expected=side.read_text().split()[0]
  raw=hashlib.sha256(lzma.decompress(p.read_bytes())).hexdigest()
  assert raw==expected,(p,expected,raw)
  compressed.append(dict(path=str(p.relative_to(E)),raw_sha256=raw))
 rows=[]
 for p in sorted(E.rglob('*')):
  assert p.name!='__pycache__'
  if not p.is_file()or p.name=='NHH_FILES.json':continue
  assert p.stat().st_size<=20_000_000,p
  rows.append(dict(path=str(p.relative_to(E)),bytes=p.stat().st_size,sha256=sha(p)))
 changed=[p for p in subprocess.check_output(['git','diff','--name-only','06fd12bd2e2^','HEAD'],cwd=E).decode().splitlines()if p]
 assert all(p.startswith('evidence/q-field-rows-20261106/')for p in changed)
 result=dict(status='PASS',source_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=E).decode().strip(),self_excluded='NHH_FILES.json',files=rows,total_bytes=sum(x['bytes']for x in rows),compressed_inputs=compressed,only_own_evidence_changed=True,static_gate_pass=True,formal_replay_repeated=False,no_file_over_20_MB=True,no_pycache=True)
 (E/'NHH_FILES.json').write_text(json.dumps(result,indent=1)+'\n')
 print(json.dumps(dict(status='PASS',files=len(rows),compressed_verified=len(compressed),bytes=result['total_bytes'],static_gate=True)))
