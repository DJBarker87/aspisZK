from pathlib import Path
import json,hashlib,re,collections
from std_parser import tokens,index,context_key
E=Path(__file__).resolve().parent;items=json.loads((E/'STD-REACHED.json').read_text());files=json.loads((E/'STD-SOURCE-HASHES.json').read_text());cache={};rows=[]
for r in items:
 rel=r['library_path']
 if not rel:continue
 row=dict(r)
 if not rel.startswith(('core/','std/','alloc/')):
  row['status']='KANI TOOL MODEL';rows.append(row);continue
 if '::intrinsics::' in r['name'] and rel=='core/src/intrinsics/mod.rs':
  row['status']='INTRINSIC: V370; declaration comparison retained separately';rows.append(row);continue
 if rel not in cache:
  a=(E/'std-sources/kani'/rel).read_bytes();b=(E/'std-sources/deployed'/rel).read_bytes();assert hashlib.sha256(a).hexdigest()==files[rel]['kani_sha256'];assert hashlib.sha256(b).hexdigest()==files[rel]['deployed_sha256'];cache[rel]=(index(a.decode()),index(b.decode()))
 aa,bb=cache[rel];line=int(r['location'].get('line',0));cand=[f for f in aa if f['start']<=line<=f['end']]
 if cand:
  width=min(f['end']-f['start']for f in cand);cand=[f for f in cand if f['end']-f['start']==width]
 if len(cand)!=1:
  row.update(status='UNRESOLVED OLD BODY: transfer withheld',old_candidates=cand);rows.append(row);continue
 a=cand[0];bs=[f for f in bb if f['name']==a['name']and f['macros']==a['macros']and context_key(f)==context_key(a)];exact=[f for f in bs if tokens(f['signature'])==tokens(a['signature'])]
 if exact:bs=exact
 row['kani_item']=a
 if bs and (len(bs)==1 or all(tokens(f['body'])==tokens(bs[0]['body'])for f in bs)):
  row['deployed_item']=bs[0];row['status']='IDENTICAL BODY TOKENS'if tokens(a['body'])==tokens(bs[0]['body'])else'DIFFERENT BODY TOKENS: structural argument required';row['signature_identical']=tokens(a['signature'])==tokens(bs[0]['signature'])
 else:row.update(status='UNRESOLVED DEPLOYED BODY: transfer withheld',deployed_candidates=bs)
 rows.append(row)
names=set()
for r in rows:
 r['intrinsic_names_in_recovered_bodies']=sorted(set(re.findall(r'\bintrinsics::(?:\{[^}]*\}|([A-Za-z_]\w*))',r.get('kani_item',{}).get('body','')+'\n'+r.get('deployed_item',{}).get('body','')))-{''});names.update(r['intrinsic_names_in_recovered_bodies'])
 if r['status'].startswith('INTRINSIC'):names.add(r['name'])
result={'gate':'K79200','method':'Exact code-symbol listing, source line -> smallest source fn; same declaration/enclosing impl/trait/macro; tree-sitter leaf tokens exclude comments. Context-only const eligibility normalized as in the pinned D540 parser; no body normalization or renaming. Unresolved macro-expanded ordinary items withhold transfer.','source_authority':'STD-SOURCE-AUTHORITY.reused.json; exact official nightly component, SHA checked, no installation','counts':dict(collections.Counter(r['status']for r in rows)),'deployed_transfer':'WITHHELD','intrinsic_boundary':'V370 / D381/D386 retained; no new trust field','rows':rows}
result['recorded_intrinsic_names']=sorted(names);result['intrinsic_caveat']='Names from exact code-symbol declarations and recovered old/new ordinary bodies. Unresolved macro/old-body mappings remain OPEN; no complete intrinsic or std-transfer clearance is claimed.'
(E/'STD-PARITY.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result['counts']))
for r in rows:
 if r['status'].startswith('DIFFERENT'):print(r['name'],r['library_path'])
