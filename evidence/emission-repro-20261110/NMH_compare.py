#!/usr/bin/env python3
"""Fail-closed provenance classification: exact bytes or NHR documented Types adaptation.
A diagnostic partial definition match is never a blob reproduction verdict.
"""
from pathlib import Path
import json,lzma,hashlib,subprocess,re,difflib,collections,base64,tomllib
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def definitions(s):
 # Exact same declaration segmentation as NKT_checker.py lines 146-162.
 ds=list(re.finditer(r'(?m)^(?:(?:noncomputable|private|protected) )?(def|theorem|lemma|abbrev|structure|inductive)\s+([^\s(]+)',s));out={}
 for i,m in enumerate(ds):
  end=ds[i+1].start() if i+1<len(ds) else len(s)
  out[m[2]]=dict(kind=m[1],sha256=sha(s[m.start():end].encode()),text=s[m.start():end])
 return out
def nhr_types(s):
 s=re.sub(r'\bdiscriminant isize,?\s*','',s)
 return re.sub(r'@\[\]\s*\n','',s)
def load(p):return json.loads(lzma.decompress(p.read_bytes()) if p.suffix=='.xz' else p.read_bytes())
def main():
 inv=load(E/'NMH_INVENTORY.json');plan=load(E/'NMH_PLAN.json');impact={b['blob']:b for b in load(E/'NMH_ROW_IMPACT.json.xz')['blobs']};groups={h:g for g in plan['groups'] for h in g['members']}
 payload=load(E/'NMH_FROZEN_PAYLOAD.json.xz');crate_names=set()
 for p,b in payload.items():
  if p.endswith('Cargo.toml'):
   doc=tomllib.loads(base64.b64decode(b).decode());pkg=doc.get('package',{})
   if 'name' in pkg:crate_names.add(pkg['name'].replace('-','_'))
 outputs=[];runs={};tool_counts=collections.Counter()
 for r in plan['runs']:
  a=r['run'];rec=E/a/'receipt.json';pins=E/(a+'_emitted')/'NHR_PINS.json'
  if rec.exists():runs[a]=dict(receipt=load(rec),pins=load(pins) if pins.exists() else {},spec=r)
  for f in (E/(a+'_emitted')/'raw').rglob('*'):
   if not f.is_file() or not (f.name.endswith('Funs.lean') or f.name.endswith('Types.lean') or f.name.endswith('Funs.lean.xz') or f.name.endswith('Types.lean.xz')):continue
   if not pins.exists() or load(pins).get('aeneas_exit')!=0 or a not in runs or runs[a]['receipt']['exit_status']!=0:continue
   if load(pins).get('lock_after')!=load(pins).get('lock_before'):continue
   b=lzma.decompress(f.read_bytes()) if f.suffix=='.xz' else f.read_bytes();outputs.append(dict(run=a,path=str(f.relative_to(E)),hash=sha(b),bytes=b,defs=definitions(b.decode()),types=f.name in ['Types.lean','Types.lean.xz']))
 if (E/'NMH_TOOL_ATTEMPTS.jsonl').exists():
  for line in (E/'NMH_TOOL_ATTEMPTS.jsonl').read_text().splitlines():tool_counts[json.loads(line)['tool']]+=1
 result=[];details=[]
 for z in inv['blobs']:
  h=z['blob'];g=groups[h];old=subprocess.check_output(['git','show',inv['revision']+':'+z['paths'][0]]);assert sha(old)==h;ds=definitions(old.decode())
  is_types='type definitions' in old.decode().split('namespace')[0]
  candidates=[o for o in outputs if o['types']==is_types and o['run'] in {r['run'] for r in plan['runs'] if h in r['members']}]
  # Native definitions from other probes can be recorded, but do not establish packet configuration.
  full=next((o for o in outputs if o['bytes']==old),None);norm=None
  if not full:
   norm=next((o for o in candidates if o['types'] and nhr_types(o['bytes'].decode())==old.decode()),None)
  comparisons=[]
  for o in candidates:
   common=set(ds)&set(o['defs']);same=[n for n in common if ds[n]['sha256']==o['defs'][n]['sha256']];different=sorted(common-set(same))
   comparisons.append(dict(run=o['run'],path=o['path'],reproduced_hash=o['hash'],same_definitions=sorted(same),different_definitions=different,missing_definitions=sorted(set(ds)-set(o['defs'])),additional_definitions=sorted(set(o['defs'])-set(ds)),full_byte_identical=o['bytes']==old))
  comparisons.sort(key=lambda c:(-len(c['same_definitions']),len(c['missing_definitions']),len(c['different_definitions'])))
  corresponding=[o for o in candidates if not runs[o['run']]['spec'].get('diagnostic_only') and not runs[o['run']]['spec'].get('repairs')]
  corresponding_paths={o['path'] for o in corresponding}
  best_corresponding=next((c for c in comparisons if c['path'] in corresponding_paths),None)
  chosen=full or norm or next((o for o in corresponding if best_corresponding and o['path']==best_corresponding['path']),None)
  relevant=[r for r in plan['runs'] if h in r['members']];attempted=[r['run'] for r in relevant if r['run'] in runs];not_done=[r['run'] for r in relevant if r['run'] not in runs]
  absent_crates=[c for c in z['crate_header'] if c not in crate_names]
  if full or norm:verdict='REPRODUCED';reason='BYTE_IDENTICAL' if full else 'NHR_parameterize.py documented discriminant metadata removal only'
  elif absent_crates:
   verdict='NOT_REPRODUCED';reason='Emission names source/reference crate(s) absent from frozen manifest closure: '+','.join(absent_crates)+'. Native projections cannot reconstruct an uncommitted/outlined driver.';chosen=None
  elif chosen:verdict='DIFFERS';reason='Committed bytes differ from emitted bytes; no permitted normalization establishes identity. Candidate configurations/projections do not establish historical origin.'
  else:
   verdict='NOT_REPRODUCED'
   if not_done:reason='Planned extraction not yet attempted: '+','.join(not_done)
   elif candidates:reason='Only diagnostic native-definition projections are available; the historical full extraction configuration or driver remains unrecovered. Partial matches/differences are retained separately, not a DIFFERS verdict.'
   elif attempted:reason='Tool/configuration failed before a corresponding emission; see run receipts.'
   elif g['configuration_candidates']:reason='Archived configuration selects a reference/outlined function or crate absent from frozen release; frozen source cannot supply that driver.'
   else:reason='Missing full historical crate/features/opacity/root configuration; source annotations alone do not define an extraction run.'
  diff=None
  if verdict=='DIFFERS':
   diff='NMH_DIFFS/'+h+'.diff.xz';raw=''.join(difflib.unified_diff(old.decode().splitlines(True),chosen['bytes'].decode().splitlines(True),fromfile=z['paths'][0],tofile=chosen['path'])).encode();p=E/diff;p.write_bytes(lzma.compress(raw,preset=6));p.with_suffix('.sha256').write_text(sha(raw)+'\n')
  result.append(dict(blob=h,group=g['group'],run=chosen['run'] if chosen else None,attempted_runs=attempted,diagnostic_runs=sorted({o['run'] for o in candidates if o not in corresponding}),definition_comparisons='NMH_DEFINITION_COMPARISONS.json.xz',verdict=verdict,reason=reason,committed_hash=h,reproduced_hash=chosen['hash'] if chosen else None,reproduced_path=chosen['path'] if chosen else None,committed_paths=z['paths'],normalization=None if not norm else 'NHR_parameterize.py discriminant metadata removal',normalized_hash=sha(nhr_types(norm['bytes'].decode()).encode()) if norm else None,diff=diff,affected_CLOSED_rows=impact[h]['affected_CLOSED_rows'],impact_scope=impact[h]['mapping'],known_defect='NKT-F1 / ruling (bc) post-loop return family' if any('batch_tree' in a['name'] for a in z['annotations']) else None))
  details.append(dict(blob=h,definitions={n:{k:v for k,v in d.items() if k!='text'} for n,d in ds.items()},comparisons=comparisons))
 retained_diffs={r['diff'] for r in result if r['diff']}
 for f in (E/'NMH_DIFFS').glob('*.diff.xz'):
  if str(f.relative_to(E)) not in retained_diffs:
   f.unlink();f.with_suffix('.sha256').unlink()
 packet=dict(schema=1,target_established=False,counts=dict(collections.Counter(r['verdict'] for r in result)),budget_used=dict(Charon=tool_counts['charon'],Aeneas=tool_counts['aeneas'],Lean=0,Kani=0),blobs=result)
 (E/'NMH_PROVENANCE.json').write_text(json.dumps(packet,indent=2)+'\n')
 raw=json.dumps(details,indent=2).encode();(E/'NMH_DEFINITION_COMPARISONS.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NMH_DEFINITION_COMPARISONS.json.sha256').write_text(sha(raw)+'\n')
 print(json.dumps(dict(counts=packet['counts'],budget_used=packet['budget_used'],completed_runs=len(runs))))
if __name__=='__main__':main()
