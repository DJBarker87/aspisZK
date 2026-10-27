import pathlib,json,subprocess,shlex
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume7'
script='''import pathlib,json,sys
rs=json.load(sys.stdin);p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-reach-20261027/lean/objects');print(json.dumps([dict(r,private_exists=(p/pathlib.Path(*r['module'].split('.')).with_suffix('.olean')).is_file()) for r in rs],indent=2))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],input=(E/'project-closure.json').read_text(),text=True,capture_output=True,check=True)
(E/'private-closure-availability.json').write_text(r.stdout);rows=json.loads(r.stdout);print('private missing',len([r for r in rows if not r['private_exists']]),'pinned missing',len([r for r in rows if not r['private_exists'] and r['authority']!='h5']))
