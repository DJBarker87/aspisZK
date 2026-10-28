from pathlib import Path
import json,sys,hashlib,re
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NCE_host as h
print('Read-only final object pinning',flush=True)
r=h.remote_py(f'''from pathlib import Path
import json,hashlib,subprocess,re
out={{}}
for label,root in [('cache',{h.CACHE!r}),('coherent',{h.C!r}),('aeneas',{(h.C+'/objects/Aeneas')!r})]:
 out[label]={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size) for p in Path(root).rglob('*.olean')}}
p=Path({(h.C+'/objects/Aeneas.olean')!r});out['aeneas'][str(p)]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
rows=subprocess.check_output(['ps','-eo','args='],text=True).splitlines()
out['live_own_runners']=[x for x in rows if re.match(r'^(?:/usr/bin/)?python3 S2W_(?:run|lean)_host[.]py NCE_',x.strip()) or (re.match(r'^(?:[^ ]*/)?(?:lean|lake)(?: |$)',x.strip()) and 'NCE_' in x)]
b=Path({h.B!r})
out['L012_recovery']={{n:(b/'NCE_L012'/n).read_text() for n in ['receipt.json','stdout.log','time.log'] if (b/'NCE_L012'/n).is_file()}}
print(json.dumps(out))''')
assert r.returncode==0,r.stderr
(E/'NCE_RECOVERY_FINAL_PINS.json').write_text(r.stdout)
final=json.loads(r.stdout);initial=json.loads((E/'NCE_INITIAL_HOST_PINS.json').read_text())
all_expected={p:v for group in initial.values() for p,v in group.items()}
all_actual={p:v for k,group in final.items() if k in initial for p,v in group.items()}
bad=[p for p,v in all_expected.items() if p not in all_actual or all_actual[p]['sha256']!=v['sha256']]
# Final statement audit directly pins every new theorem module; final axioms
# audit pins that statement object. Compare these observed actual imports too.
for a in ['NCE_L059','NCE_L060']:
 rc=json.loads((E/a/'receipt.json').read_text())
 for name,v in rc['deps_fingerprint']['selected_objects'].items():
  if name.startswith('NCE_'):
   p=v['path']
   if p not in all_actual or all_actual[p]['sha256']!=v['sha256']:bad.append(p)
assert not bad,bad
assert not final['live_own_runners'],final['live_own_runners']
summary=dict(reused_objects_checked=len(all_expected),mismatches=bad,live_own_runners=final['live_own_runners'],
 initial_counts={k:len(v) for k,v in initial.items()},final_counts={k:len(final[k]) for k in initial},
 new_objects={p:v for p,v in all_actual.items() if Path(p).name.startswith('NCE_')},
 L012_terminal_recovery_found=bool(final['L012_recovery']),cache_retained=True,headline_replay=False)
(E/'NCE_RECOVERY_OBJECT_AUDIT.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='new_objects'}),flush=True)
