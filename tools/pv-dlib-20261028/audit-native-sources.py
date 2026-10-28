from pathlib import Path
import json,subprocess,hashlib,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028';D='/home/dombarker/project-offloads/codex-pv-dlib-20261028';H='dombarker@100.108.41.90'
name=sys.argv[1];assert name.replace('-','').isalnum()
pins=json.loads((E/'native-prefix-pins.json').read_text());core=json.loads((E/'encoder-core-source-check.json').read_text())
code="""from pathlib import Path
import hashlib,json,datetime
b=Path(DIR);reg=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f');rows=[]
for j in PINS:
 source=(reg/j['crate']/j['relative_path']).read_bytes();actual=(b/'native'/j['crate']/j['relative_path']).read_bytes()
 ok=hashlib.sha256(source).hexdigest()==j['sha256'] and actual.startswith(source)
 rows.append(dict(**j,prefix_matches=ok,actual_sha256=hashlib.sha256(actual).hexdigest(),extra_bytes=len(actual)-len(source)))
root=Path(COREROOT);cr=[]
for j in CORE:
 h=hashlib.sha256((root/j['path']).read_bytes()).hexdigest();cr.append(dict(path=j['path'],expected=j['expected_sha256'],actual=h,ok=h==j['expected_sha256']))
print(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),native_prefixes=rows,core=cr,all_match=all(j['prefix_matches'] for j in rows) and all(j['ok'] for j in cr)),indent=2))
""".replace('DIR',repr(D)).replace('PINS',repr(pins)).replace('COREROOT',repr(core['read_only_source_root'])).replace('CORE',repr(core['files']))
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);(E/f'native-source-audit-{name}.json').write_text(r.stdout);assert j['all_match'];print(len(j['native_prefixes']),len(j['core']),'sources matched')
