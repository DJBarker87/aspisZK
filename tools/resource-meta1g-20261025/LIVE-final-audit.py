"""Local evidence/source inventory; no collector replay or host access."""
import ast,hashlib,importlib.util,json,subprocess,sys,time,resource,platform
from pathlib import Path
START=time.monotonic();ROOT=Path(__file__).resolve().parents[2];HERE=Path(__file__).resolve().parent;OUT=ROOT/'evidence/resource-meta1g-20261025'
def pin(b):return dict(sha256=hashlib.sha256(b).hexdigest(),size=len(b))
spec=importlib.util.spec_from_file_location('capture',HERE/'LIVE-EVIDENCE-capture.py');capture=importlib.util.module_from_spec(spec);spec.loader.exec_module(capture)
seal=json.loads((OUT/'LIVE-identity-seal.json').read_text())
for name,expected in seal['operational'].items():
    b=(HERE/name).read_bytes();assert pin(b)==expected
    assert b==subprocess.check_output(['git','show','13abf7fe51:tools/resource-meta1g-20261025/'+name],cwd=ROOT)
for name,expected in seal['helpers'].items():
    b=(HERE/name).read_bytes();assert pin(b)==expected['new'];text=b.decode()
    for old,new in reversed(seal['substitutions']):text=text.replace(new,old)
    old=subprocess.check_output(['git','show','45d137dd34:tools/resource-rss-go-v3-20261025/'+name.removeprefix('LIVE-')],cwd=ROOT)
    assert text.encode()==old and ast.dump(ast.parse(text),include_attributes=True)==ast.dump(ast.parse(old),include_attributes=True)
index=json.loads((OUT/'LIVE-EVIDENCE-index.json').read_text());assert len(index['inventory'])==29
for frame in index['frames']:
    b=(OUT/frame['path']).read_bytes();assert pin(b)=={k:frame[k] for k in ('sha256','size')};assert len(b)<=4_500_000
locations=json.loads((OUT/'LIVE-EVIDENCE-transport-location.json').read_text())
assert locations['count']==len(locations['files'])==2511
for name,record in locations['files'].items():
    assert pin(Path(record['path']).read_bytes())==index['transport_pins'][name]
inside=capture.load('inside-scope-report.json');own=inside['decision']['scope_binding']['self_identity']['path']
counts={}
for label in ('before','after'):
    observation=inside['decision'][label+'_observation']
    assert observation['frontier'].count(own)==1
    assert observation['bounded_reserved_bytes']<55*2**30
    counts[label]=dict(own_occurrences=observation['frontier'].count(own),bounded_reserved_bytes=observation['bounded_reserved_bytes'],frontier_count=len(observation['frontier']))
rows=[r for r in inside['original_legacy']['cgroups'] if r['path']==own]
assert len(rows)==1 and rows[0]['charged_bytes']==2**30 and inside['decision']['additional_bytes']==0
inventory={}
for directory in (HERE,OUT):
    for path in sorted(directory.iterdir()):
        if path.is_file():
            b=path.read_bytes();assert len(b)<=5_000_000
            inventory[str(path.relative_to(ROOT))]=pin(b)
u=resource.getrusage(resource.RUSAGE_SELF)
receipt=dict(command=[sys.executable,'-B',str(Path(__file__).resolve())],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),exit=0,wall_seconds=time.monotonic()-START,peak_rss_bytes=u.ru_maxrss*(1 if platform.system()=='Darwin' else 1024),swap=u.ru_nswap,print_axioms='N/A',operational_exact_13ab=True,helpers_identity_only_exact_45d=True,full_ast_attributes=True,own_cap_count=counts,own_legacy_charge=rows[0]['charged_bytes'],inside_additional_bytes=0,inventory_count=len(index['inventory']),transport_count=len(locations['files']),frames_count=len(index['frames']),files=inventory,notes=['This is a local pin/frontier/inventory audit, not an unchanged suite or collector replay','Wrapper actual bytes included here; prior new-data driver receipt copied helper retained historical offline-driver pin list','Runtime/source closure is captured original metadata provenance, not a fresh deployed binary identity gate'])
with (OUT/'LIVE-final-audit.json').open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='files'}))
