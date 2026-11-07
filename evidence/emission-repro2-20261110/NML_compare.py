"""Fail-closed whole-blob reproduction and conservative NMH lexical row impact."""
from pathlib import Path
import json,lzma,hashlib,re,collections,subprocess
E=Path(__file__).resolve().parent;OLD=E.parent/'emission-repro-20261110'
sha=lambda b:hashlib.sha256(b).hexdigest()
def load(p):return json.loads(lzma.decompress(p.read_bytes()) if p.suffix=='.xz' else p.read_bytes())
def write(n,d): (E/n).write_text(json.dumps(d,indent=2)+'\n')
def normalized(b):
 s=re.sub(r'\bdiscriminant isize,?\s*','',b.decode());return re.sub(r'@\[\]\s*\n','',s).encode()
def definitions(s):
 ms=list(re.finditer(r'(?m)^(?:(?:noncomputable|private|protected) )?(def|theorem|lemma|abbrev|structure|inductive)\s+([^\s(]+)',s));return {m[2]:dict(kind=m[1],sha256=sha(s[m.start():ms[i+1].start() if i+1<len(ms) else len(s)].encode()))for i,m in enumerate(ms)}
def main():
 old=load(OLD/'NMH_PROVENANCE.json');plan=load(E/'NML_PLAN.json');outputs=[];attempts={};tools=collections.Counter();detail=[]
 for q in plan['runs']:
  a=q['run'];p=E/a/'receipt.json';n=E/(a+'_emitted')/'NHR_PINS.json'
  if p.exists():attempts[a]=load(p)
  if not p.exists() or not n.exists():continue
  pin=load(n)
  for tool in ['charon','aeneas']:
   if (E/(a+'_emitted')/(tool+'_receipt.json')).exists():tools[tool]+=1
  if a=='NML_E001' and (E/'NML_ADMISSION_FINDING.json').exists():continue
  if attempts[a]['exit_status']!=0 or pin.get('charon_exit')!=0 or pin.get('aeneas_exit')!=0 or pin.get('lock_before')!=pin.get('lock_after'):continue
  for f in (E/(a+'_emitted')/'raw').rglob('*'):
   if not f.is_file() or not f.name.endswith(('.lean','.lean.xz')):continue
   b=lzma.decompress(f.read_bytes()) if f.suffix=='.xz' else f.read_bytes()
   outputs.append(dict(run=a,path=str(f.relative_to(E)),sha256=sha(b),normalized_sha256=sha(normalized(b)) if 'Types.lean' in f.name else None,data=b,spec=q))
 if (E/'NML_TOOL_ATTEMPTS.jsonl').exists():
  tools=collections.Counter(json.loads(line)['tool'] for line in (E/'NML_TOOL_ATTEMPTS.jsonl').read_text().splitlines())
 result=[];diffs=load(E/'NML_DIFFS_CLASSIFIED.json') if (E/'NML_DIFFS_CLASSIFIED.json').exists() else dict(blobs=[])
 classified={b['blob']:b for b in diffs['blobs']}
 for b in old['blobs']:
  h=b['blob'];z=dict(b);z['inherited_NMH_verdict']=b['verdict'];z['NML_runs']=[q['run'] for q in plan['runs'] if h in q['members']];z['NML_attempts']=[a for a in z['NML_runs'] if a in attempts]
  raw=subprocess.check_output(['git','show','HEAD:'+b['committed_paths'][0]]);assert sha(raw)==h
  ds=definitions(raw.decode());candidates=[o for o in outputs if h in o['spec']['members']];comparisons=[]
  for o in candidates:
   od=definitions(o['data'].decode());common=ds.keys()&od.keys();comparisons.append(dict(run=o['run'],path=o['path'],same=sorted(n for n in common if ds[n]==od[n]),different=sorted(n for n in common if ds[n]!=od[n]),missing=sorted(ds.keys()-od.keys()),additional=sorted(od.keys()-ds.keys())))
  detail.append(dict(blob=h,definitions=ds,comparisons=comparisons))
  match=next((o for o in outputs if o['sha256']==h),None);norm=None if match else next((o for o in outputs if o['normalized_sha256']==h),None)
  o=match or norm
  if o:
   q=o['spec'];z.update(verdict='REPRODUCED_FROM_ARCHIVE',reason='BYTE_IDENTICAL' if match else 'Only admitted NHR_parameterize.py discriminant-metadata normalization',run=o['run'],reproduced_hash=o['sha256'],reproduced_path=o['path'],normalization=None if match else 'NHR_parameterize.py discriminant metadata removal',input=dict(directory=q['reference_directory'],source_sha256=q['reference_sha256'],source_git_blob=q['configuration']['source']['git_blob'],basis=q['reference_basis'],manifest_sha256=q['manifest_sha256'],manifest_basis=q['manifest_basis']))
  elif b['verdict']=='REPRODUCED':
   z.update(verdict='REPRODUCED_FROM_ARCHIVE',reason='Inherited exact NMH frozen-input reproduction; unchanged archived inputs/receipts, not rerun',input=dict(origin='Frozen Git source through NMH NHR staging',manifest='evidence/emission-repro-20261110/NMH_STAGING_MANIFEST.json',receipt=b['run']+'/receipt.json'))
  elif classified.get(h,{}).get('classification') in ['SEMANTIC','NON-SEMANTIC']:
   z.update(verdict='DIFFERS_SEMANTIC' if classified[h]['classification']=='SEMANTIC' else 'DIFFERS_NONSEMANTIC',reason=classified[h]['reason'],classification_evidence=classified[h])
  else:
   z.update(verdict='NOT_REPRODUCED',reason=('NMH byte difference remains UNCLASSIFIED: '+classified.get(h,{}).get('reason','no Lean definitional-equality evidence') if b['verdict']=='DIFFERS' else ('Archive rerun differs or fails; see exact definition comparisons and receipts' if z['NML_attempts'] else 'No admitted archive rerun: '+b['reason'])))
  if 'NML_E001' in z['NML_attempts']:
   z['excluded_NML_attempts']=['NML_E001'];z['admission_finding']='NML_ADMISSION_FINDING.json'
   if z['verdict']=='NOT_REPRODUCED':z['reason']='E001 excluded from provenance credit: owned-client restart rechecked after 15.095 seconds instead of the required 180; no unchanged rerun. Original bytes also differ in the empty-Types import; see NML_E001_blob.diff.xz.'
  result.append(z)
 nonrepro=[b for b in result if b['verdict']!='REPRODUCED_FROM_ARCHIVE'];rows=sorted({r for b in nonrepro for r in b['affected_CLOSED_rows']})
 packet=dict(schema=1,target_established=False,counts=dict(collections.Counter(b['verdict'] for b in result)),budget_used=dict(Charon=tools['charon'],Aeneas=tools['aeneas'],Lean=sum((E/a/'receipt.json').exists() for a in ['NML_L%03d'%i for i in range(1,21)]),Kani=0),blobs=result,conservative_affected_CLOSED_rows=rows,affected_CLOSED_count=len(rows),rootless_CLOSED_unassessed=['TX1:059','TX2:040'],impact_method='Reuse NMH exact lexical declaration/scoped-private alias intersection with 1,081 archived CLOSED-root reachability lists; union remaining non-reproduced blob impacts. Historical aliases retained; no selected-source/object claim.')
 write('NML_PROVENANCE.json',packet)
 raw=json.dumps(detail,indent=2).encode();(E/'NML_DEFINITION_COMPARISONS.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NML_DEFINITION_COMPARISONS.json.sha256').write_text(sha(raw)+'\n')
 print(json.dumps({k:packet[k] for k in ['counts','budget_used','affected_CLOSED_count']}))
if __name__=='__main__':main()
