"""Read-only, pinned input collection for the PLIB preparatory job."""
import hashlib, json, lzma, pathlib, re, subprocess

E = pathlib.Path('evidence/pv-lib-20261107')
E.mkdir(exist_ok=True)
P = json.loads((E/'INPUT_REVISIONS.json').read_text())
def show(rev, path):
    return subprocess.check_output(['git','show',rev+':'+path])
def sha(b): return hashlib.sha256(b).hexdigest()
inputs = []
def save(label, rev, path):
    b = show(rev,path)
    dest = 'inputs/'+label+'.xz'
    (E/dest).write_bytes(lzma.compress(b))
    inputs.append(dict(revision=rev,path=path,archive=dest,sha256=sha(b),bytes=len(b)))
    return b
ledger = json.loads(save('ledger',P['research'],'design/PRIVACY-FN-LEDGER-20261108.json'))
rows = {r['id']:r for r in ledger['rows']}
for b,rev in P.items():
    if b != 'research': save(b.split('/')[1]+'-HANDOFF',rev,'HANDOFF.md')
for path in ['evidence/rowspec-lead-20261107/RSL_INDEX.md',
             'evidence/rowspec-lead-20261107/RSL_REVISION2.md',
             'evidence/rowspec-lead-20261107/RSL_REVISION3.md',
             'evidence/lib-map-20261107/LIB0_MAP.md',
             'evidence/lib-map-20261107/LIB0_BRIEF.md']:
    save(path.split('/')[-1],P['research'],path)
common=pathlib.Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad')
for name in ['pv-common.txt','plib-open-rows.txt']:
    b=(common/name).read_bytes(); (E/('inputs/'+name+'.xz')).write_bytes(lzma.compress(b))
    inputs.append(dict(path=str(common/name),archive='inputs/'+name+'.xz',sha256=sha(b),bytes=len(b)))
open_ids=[l.split()[0] for l in (common/'plib-open-rows.txt').read_text().splitlines()]
assert set(open_ids)=={r['id'] for r in rows.values() if r['status']!='CLOSED'}
assert len(open_ids)==29
statements={
 'thread:f6':('codex/pv-evhB-20261103','PV_FN_THREAD_f6Joins'),
 'thread:f361':('codex/pv-w3-20261108','PV_FN_THREAD_f361Statement'),
 'slice:f21':('codex/pv-stx-20261104','PV_STX2_ToVecCallSpecification'),
 'slice:f7':('codex/pv-w2-20261108','PV_FN_SLICE_f7_Statements'),
 'thread:f170':('codex/pv-w4-20261108','PV_FN_THREAD_f170Statement'),
 'thread:f17':('codex/pv-w4-20261108','PV_FN_THREAD_f17Statement'),
 'thread:f2':('codex/pv-w4-20261108','PV_FN_THREAD_f2Statement'),
 'thread:f5':('codex/pv-w4-20261108','PV_FN_THREAD_f5Statement')}
for rid,(branch,module) in statements.items(): save(module,P[branch],'lean/'+module+'.lean')
for name in ['PV_THR2_SourceStoreInterpreter','PV_THR2_SourceStoreLibrary',
             'PV_THR2_SourceStoreNative','PV_THR2_SourceStoreAgreement']:
    save(name,P['codex/pv-w4-20261108'],'lean/'+name+'.lean')
for rid in open_ids:
    src=rows[rid]['source']; path=src['syntax']
    if path: save('syntax-'+rid.replace(':','-'),src['revision'],path)
providers={}
for rid,r in rows.items():
    c=r.get('closure')
    if not c: continue
    s=c['source']; raw=save('root-'+rid.replace(':','-').replace('/','_').replace('"',''),s['revision'],s['path'])
    providers[rid]=dict(theorem=c['theorem'],branch=c['branch'],revision=s['revision'],
        source=s['path'],sha256=sha(raw),definitions=re.findall(
        r'^(?:noncomputable )?(?:def|abbrev|structure|inductive) ([A-Za-z0-9_\'.]+)',raw.decode(),re.M),
        raw_audit=c.get('raw_audit'),combined_cohort=c.get('combined_cohort'))
order=[];active=[];seen=set();cycles=[]
def dfs(rid):
    if rid in active: cycles.append(active[active.index(rid):]+[rid]);return
    if rid in seen:return
    active.append(rid)
    for c in rows[rid]['callees']:dfs(c)
    active.pop();seen.add(rid);order.append(rid)
for rid in ['thread:OwnInit','slice:f0']:dfs(rid)
(E/'INPUT_MANIFEST.json').write_text(json.dumps(inputs,indent=2)+'\n')
(E/'PROVIDERS.json').write_text(json.dumps(providers,indent=2)+'\n')
(E/'DEPENDENCIES.json').write_text(json.dumps(dict(order=order,cycles=cycles,
    rows=[dict(id=r['id'],status=r['status'],name=r['source_name'],callees=r['callees'],
               sites=r['call_sites'],contract=r.get('contract'),source=r['source']) for r in rows.values()]),indent=2)+'\n')
print('Pinned',len(inputs),'inputs;',len(providers),'CLOSED providers;',len(open_ids),'open rows; cycles:',cycles)
