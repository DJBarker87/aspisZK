import pathlib,json,subprocess,sys,shlex
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume7'
for a,row in enumerate(json.loads((E/'public-import-added-modules.json').read_text()),39474):
 m=row['module'];code=f'''import pathlib,json
p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-reach-20261027/lean/objects')/pathlib.Path({m.replace('.','/')!r});removed=[]
for q in p.parent.glob(p.name+'.*'):
 if q.is_symlink():removed.append(dict(path=str(q),target=str(q.readlink())));q.unlink()
print(json.dumps(removed))
'''
 r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True,check=True);(E/f'private-detach-{a}.json').write_text(r.stdout)
 p=E/'authorized-sources'/(m+'.lean.txt')
 r=subprocess.run([sys.executable,str(R/'tools/pv-reach-20261027/resume7-check.py'),str(a),m.replace('.','/'),str(p.relative_to(R))],capture_output=True,text=True)
 print(r.stdout[-2200:]+r.stderr[-500:],flush=True)
 if not (E/f'receipt-{a}.json').exists():sys.exit(r.returncode or 2)
