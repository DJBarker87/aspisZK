"""Execute the canonical recovery builder with explicit continuation scheduling.
Only EJS files are created by this adapter; canonical builder remains unchanged.
"""
from pathlib import Path
import hashlib, os
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
p=T/'EJR_build_host.py'
s=p.read_text()
assert hashlib.sha256(p.read_bytes()).hexdigest()=='57f8ce56a0415520e457df78776d473170473aa8c78c910c749dd890be168802'
assert os.environ.get('EJR_CUMULATIVE_BUILD_LIMIT')=='1600'
def replace(old,new):
 global s
 assert s.count(old)==1, old
 s=s.replace(old,new)
# Preserve valid pinned reuse aliases; replace dangling fallback aliases only.
assert s.count("if dest.resolve()==canonical:continue")==2
s=s.replace("if dest.resolve()==canonical:continue", "if dest.is_file():continue")
if os.environ.get('EJS_PROFILE'):
 profile=os.environ['EJS_PROFILE']
 assert profile in {'provider','formatter','missing'}
 if profile=='provider':
  replace("roots={'joint':J,'union':U}", "roots={'joint':J,'union':U}\nprofile_name='EJS_provider'\nroots[profile_name]=U/profile_name\nrows.extend(json.loads((T/(profile_name+'-sources.json')).read_text()))")
 elif profile=='formatter':
  replace("roots={'joint':J,'union':U}", "roots={'joint':J,'union':U}\nroots.update({n:U/n for n in ['EJS_formatter_joint','EJS_formatter_union']})\nrows.extend(json.loads((T/'EJS_formatter-sources.json').read_text()))")
 else:
  replace("roots={'joint':J,'union':U}", "roots={'joint':J,'union':U}\nroots['EJS_missing']=U/'EJS_missing'\nrows.extend(json.loads((T/'EJS_missing-sources.json').read_text()))")
if os.environ.get('EJS_PROFILE')=='missing':
 replace("def save_state(pending,reason):", """def publish_missing(r):
 if r['workspace']!='EJS_missing':return
 published=[]
 for root in [J,U]:
  for ext in ['.olean','.olean.private','.olean.server','.ir']:
   src=roots['EJS_missing']/'objects'/(r['module']+ext)
   if not src.is_file():continue
   dest=root/'objects'/(r['module']+ext)
   if dest.exists():
    if sha(dest)!=sha(src):published.append(dict(path=str(dest),status='existing different object retained',existing_sha256=sha(dest)))
    continue
   old_link=str(dest.readlink()) if dest.is_symlink() else None
   if dest.is_symlink():dest.unlink()
   dest.parent.mkdir(parents=True,exist_ok=True);os.link(src.resolve(),dest)
   published.append(dict(path=str(dest),sha256=sha(dest),source=str(src),old_dangling_link=old_link))
 with (T/'EJS_missing-publications.jsonl').open('a') as f:f.write(json.dumps(dict(module=r['module'],source_sha256=r['source_sha256'],bindings=published))+chr(10))
def save_state(pending,reason):""")
 replace("if ec==0:succeeded.add(r['key'])", "if ec==0:\n  succeeded.add(r['key']);publish_missing(r)")
 replace("context={n:sha(T/n) for n in ['EJR-namespace-bindings.json','EJR-library-published.json','EJR-library-ir-restored.json']}", "context={n:sha(T/n) for n in ['EJR-namespace-bindings.json','EJR-library-published.json','EJR-library-ir-restored.json','EJS_missing-sources.json']}")
if os.environ.get('EJS_PROFILE')=='formatter':
 replace("def try_reuse(r,ds):", """fmt_targets={'Aeneas','Aeneas/Std','Aeneas/Std/Core','Aeneas/Std/Array','Aeneas/Std/Array/ArraySlice','ImportUnionNamedDiscriminant','AspisR72Sampler/Types','AspisR72Sampler/Funs','AspisV8R19/SamplerWordRead'}
fmt_rebuild={r['key'] for r in rows if r['workspace']=='EJS_formatter_union' and r['module'] in fmt_targets and (r['key'] not in latest_by_key or latest_by_key[r['key']]['attempt']<31066)}
repair_keys.update(fmt_rebuild);succeeded.difference_update(fmt_rebuild)
def try_reuse(r,ds):
 if r['key'] in fmt_rebuild:return False""")
 replace("def try_reuse(r,ds):", "repair_keys.update(r['key'] for r in latest_by_key.values() if r['attempt'] in (31019,31020) and r['exit']==90)\ndef try_reuse(r,ds):")
 replace("context={n:sha(T/n) for n in ['EJR-namespace-bindings.json','EJR-library-published.json','EJR-library-ir-restored.json']}", "context={n:sha(T/n) for n in ['EJR-namespace-bindings.json','EJR-library-published.json','EJR-library-ir-restored.json','EJS_formatter-loader-repair.json']}")
if os.environ.get('EJS_PROFILE')=='provider':
 replace("def try_reuse(r,ds):", "repair_keys.update(r['key'] for r in latest_by_key.values() if r['key']=='EJS_provider:R1Z/CertBuildBase' and r['attempt']==31012 and r['exit']!=0)\ndef try_reuse(r,ds):")
 replace("context={n:sha(T/n) for n in ['EJR-namespace-bindings.json','EJR-library-published.json','EJR-library-ir-restored.json']}", "context={n:sha(T/n) for n in ['EJR-namespace-bindings.json','EJR-library-published.json','EJR-library-ir-restored.json','EJS_provider-path-repair.json']}")
replace("pending=[r for r in rows if r['key'] not in attempted or r['key'] in repair_keys]", """assert 30800 <= attempt <= 31600, attempt
assert len(past) >= 800
excluded={'R1Z/EventsR1P2','R1Z/SimCostOuterRetry6'}
pending=[r for r in rows if (r['key'] not in attempted or r['key'] in repair_keys) and r['module'] not in excluded]
collisions=[]
for r in pending[:]:
 obj=roots[r['workspace']]/'objects'/(r['module']+'.olean')
 if r['workspace'] in ('joint','union') and obj.is_file() and not obj.is_symlink():
  collisions.append(dict(key=r['key'],path=str(obj),object_sha256=sha(obj),source_sha256=r['source_sha256'],reason='Unreceipted regular object appeared in shared output root; preserve and do not overwrite or adopt it.'))
  pending.remove(r)
(T/'EJS_preserved-existing-objects.json').write_text(json.dumps(collisions,indent=2)+chr(10))
bykey={r['key']:r for r in rows}
priority=set()
def mark(k):
 if k in priority or k not in bykey:return
 priority.add(k)
 r=bykey[k]
 for m in r['imports']:
  own=r['workspace']+':'+m
  if own in bykey:mark(own)
  else:
   for ws in roots:mark(ws+':'+m)
for r in rows:
 if r['module'].startswith('R1Z/') or 'ProverCommit' in r['module'] or 'PrivacyR1HeadlineDeployedReal' in r['module']:mark(r['key'])
""")
replace("ready.sort(key=lambda rd:(not rd[0]['module'].startswith('R1Z/'),rd[0]['workspace']!='joint',rd[0]['module']))", "ready.sort(key=lambda rd:(rd[0]['key'] not in repair_keys, rd[0]['key'] not in priority, not rd[0]['module'].startswith('R1Z/'),rd[0]['workspace']!='joint',rd[0]['module']))")
replace("label='EJR-'+str(attempt);admission=admit(label)", "assert 30800 <= attempt < 31600 and attempt <= 34999, attempt\n label='EJR-'+str(attempt);admission=admit(label)")
replace("budget=800,next_attempt=attempt", "budget=budget,next_attempt=attempt")
(T/'EJS_executed-builder.py').write_text(s)
exec(compile(s,str(p),'exec'),{'__name__':'__main__','__file__':str(p)})
