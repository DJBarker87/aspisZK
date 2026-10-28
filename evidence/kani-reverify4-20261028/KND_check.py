from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent
rows=json.loads((E/'KND_SCHEDULE.json').read_text());n=0
assert len(rows)==116 and len({(r['len'],r['cap'],r['size']) for r in rows})==116
for r in rows:
 assert r['len']==n and r['cap']==1768 and r['len']+r['size']<=r['cap'];n+=r['size']
assert n==1768
for i in range(38):
 text=(E/f'KND_Steps{i:02}.lean').read_text()
 actual=[dict(operation=op,len=int(n),cap=int(c),size=int(s)) for op,n,c,s in re.findall(r'⟨"([^"]+)",(\d+),(\d+),(\d+)⟩',text)]
 assert actual==(rows[i*3:(i+1)*3] if i<37 else rows[111:])
 assert not any(x in text for x in ['norm_num','simp_all','unfold','rfl','sorry'])
manifest=json.loads((E/'KND_LEAN_MANIFEST.json').read_text());assert len(manifest)==49 and len(set(manifest))==49
assert all((E/(m+'.lean')).is_file() for m in manifest)
scalar=(E/'KND_LPi_K012.lean').read_text()
assert 'schedule.filter' in scalar and 'List.mem_filter.mp' in scalar
assert 'theorem reachable : ∀ s ∈ applicable, s ∈ KND_Schedule.schedule := by decide' not in scalar
print(json.dumps(dict(check='PASS',schedule_steps=116,generated_chunks=38,lean_modules=49,final_bytes=n,scope='finite metadata checks; no large recurrence normalization')))
