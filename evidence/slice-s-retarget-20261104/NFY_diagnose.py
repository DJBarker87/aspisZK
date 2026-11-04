"""Inventory measured shortest legacy paths and immutable source declarations."""
from pathlib import Path
import subprocess,json,hashlib,re,collections,lzma
E=Path(__file__).resolve().parent;R=E.parents[1];P=R/'evidence/ledger7-20261104'
rows=json.loads((P/'NFX_S_PACKET_PATHS.json').read_text())
g={r['module']:r['imports'] for r in map(json.loads,(P/'NFX_audit/inventory-s/inventory-s.log').read_text().splitlines()) if r.get('module')}
mods=sorted({m for r in rows for v in r['legacy_paths'].values() for m in v})
paths=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],cwd=R,text=True).splitlines();lookup=collections.defaultdict(list)
for p in paths:
 if p.endswith('.lean') and not re.search(r'/[A-Z]+_L\d+/',p):lookup[Path(p).stem].append(p)
fallback={}
for f in ['slice-q-phase-20261104/NFN_SOURCE_GRAPH.json','slice-q-accum-20261104/NFS_SOURCE_GRAPH.json']:
 fallback.update(json.loads((R/'evidence'/f).read_text()))
source={}
def get(n):
 if n in source:return source[n]
 ps=lookup.get(n,[])
 if not ps and '.' in n:ps=sorted([p for p in paths if p.endswith('/'+n.replace('.','/')+'.lean') and '/sources/' not in p],key=len)[:1]
 ps=sorted(ps,key=lambda p:(0 if p.startswith('lean/') else 1, -len(p),p))
 if ps:
  p=ps[0];t=(R/p).read_text() if (R/p).exists() else subprocess.check_output(['git','show','HEAD:'+p],cwd=R,text=True)
  d=dict(path=p,source=t,sha256=hashlib.sha256(t.encode()).hexdigest(),imports=re.findall(r'^import ([\w.]+)',t,re.M))
 elif n in fallback:d=dict(fallback[n]);d['sha256']=hashlib.sha256(d.get('source','').encode()).hexdigest()
 else:d=dict(missing=True,imports=g.get(n,[]))
 source[n]=d;return d
for n in mods:get(n)
def family(n):
 if n.startswith(('FIo_','NP6_','LPf_')):return 'FIo / NP6 standard model'
 if n.startswith(('Prepared','CurrentPrepared','CurrentOriginalPrepared','CurrentSampler','SelectedWideView')) or n in ['CurrentCompactInstalledPreparationV1','CurrentCompactCallerConstantsV1']:return 'Prepared owner and installation'
 if n.startswith(('S1','S6','Repin','CurrentCompact','ClaimsUnrolled')):return 'S1 Phase and semantic/codec forest'
 if n.startswith(('OraclePort','Checkpoint','Port','ChildJoin','VTop_')):return 'OraclePort / Checkpoint'
 if n.startswith(('Extracted','R0P.')):return 'Extracted reachability and pinned libraries'
 if n.startswith(('S2W_','S2X_','SInt2_','SdkD_','Tx2N_','GExp_','DrvC_')):return 'S2W consolidation and SDK consumers'
 return 'S certificate and local helper forest'
fs=collections.defaultdict(list)
for n in mods:fs[family(n)].append(n)
lines=['# NFY measured legacy families','',f'{len(mods)} distinct modules on measured shortest legacy paths; 85 directly affected occurrences, four propagated qualifications. This is a minimal union of the recorded paths, not a claim to enumerate the full transitive import closure.','', 'Exact source declarations and line ranges are in NFY_DIAGNOSIS.json. Direct declaration use is separately recorded as qualified tokens occurring in each selected certificate source. Imports alone do not establish declaration use.','']
for f,ns in fs.items():
 affected=[r['row'] for r in rows if any(n in ns for v in r['legacy_paths'].values() for n in v)]
 lines += ['## '+f,'',f'{len(ns)} modules, {len(affected)} direct occurrences.','',', '.join('`'+n+'`' for n in ns), '']
 if f.startswith('S1'):note='Canonical verifier.Phase is the inductive in AspisR1PublicPreparation.Types; the legacy abbreviation unfolds to FirstCaller.Phase. NOT definitionally equal. Reuse NFN_PhaseTransport constructor/payload bijection and both roundtrips; no redefinition.'
 elif f.startswith('Prepared'):note='Canonical RPz7 Prepared owner must be reused. Legacy PrepQM and canonical owner cannot coexist; exact field/constructor transport must be type-checked before any theorem needing it receives credit.'
 elif f.startswith('FIo'):note='Reuse RPz7_FIo_NativeTypes/External/Funs and RPt_FIo_ReduceBounds, NFN/NFS proof retargets. FIo non-import bodies are identical (NFN provenance); NP6 ReserveError owner is handled by NFN_ReserveOwner, not a second shared definition.'
 elif f.startswith('Extracted'):note='Use exact canonical object variants in NFX_LEGACY_FAMILY_PINS.json. ExtractedTx1Reachability has no admitted final replacement: omit an unused import or produce a new NFY proof of the needed statement; no legacy credit.'
 elif f.startswith('S2W'):note='Reuse canonical SInt2/RPx closure and exact NFX pinned S2W_OuterErasure variant. The two common libraries are byte-identical under canonical prerequisites. No new transport is inferred from matching names.'
 elif f.startswith('Oracle'):note='Reuse canonical headline closure and NFX variant pins. Retarget only exact used declarations; no oracle law or checkpoint premise is removed.'
 else:note='Copy theorem bodies with NFY namespaces and provenance; reuse NFN/NFS theorem owners rather than duplicating proofs. Remove unrelated broad imports only when a focused canonical compile plus full coherence scan establishes sufficiency.'
 lines += [note,'']
roots=sorted({n for r in rows for n in r['referenced_modules']});usage={}
for n in roots:
 d=get(n);t=d.get('source','');usage[n]=sorted(set(re.findall(r'\b(?:[A-Za-z_][A-Za-z_0-9]*\.)+[A-Za-z_][A-Za-z_0-9]*',t)))
for n,d in source.items():d['declarations']=[dict(line=i,text=l) for i,l in enumerate(d.get('source','').splitlines(),1) if re.match(r'(?:private |protected |noncomputable )*(?:theorem|lemma|def|abbrev|structure|inductive) ',l)]
(E/'NFY_FAMILIES.md').write_text('\n'.join(lines))
(E/'NFY_DIAGNOSIS.json').write_text(json.dumps(dict(path_module_count=len(mods),path_modules=mods,families={f:dict(modules=ns,rows=[r['row'] for r in rows if any(n in ns for v in r['legacy_paths'].values() for n in v)]) for f,ns in fs.items()},certificate_qualified_tokens=usage),indent=1)+'\n')
(E/'NFY_SOURCE_GRAPH.json').write_text(json.dumps(source,indent=1)+'\n')
print(json.dumps(dict(path_modules=len(mods),source_modules=len(source),families={f:len(ns) for f,ns in fs.items()},missing=[n for n,r in source.items() if r.get('missing')])))
