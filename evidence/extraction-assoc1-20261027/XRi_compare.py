from pathlib import Path
import re,json,hashlib,difflib
E=Path(__file__).resolve().parent;R=E.parent.parent
paths={'cohort_Types':R/'docs/research/100bit-spend-path-20261013/lean/bridge-tx1-e5c186ba3-20261016/AspisR1PublicPreparation/Types.lean','cohort_Funs':R/'docs/research/100bit-spend-path-20261013/lean-candidates/s1-prepared-claim-carrier-bridge-20261020/sources/AspisR1PublicPreparation/Funs.lean','release_Types':E/'XRi_Types.lean.txt','release_Funs':E/'XRi_Funs.lean.txt','release_ExternalTypes':E/'XRi_TypesExternal_Template.lean.txt','release_ExternalFuns':E/'XRi_FunsExternal_Template.lean.txt'}
def sha(b):return hashlib.sha256(b).hexdigest()
def clean(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;out+=[' ',' '];i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;out+=[' ',' '];i+=2
  elif depth:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s[i:i+2]=='--':
   k=s.find('\n',i);k=len(s) if k<0 else k;out.extend(' '*(k-i));i=k
  else:out.append(s[i]);i+=1
 return ''.join(out)
def inventory(p):
 s=p.read_text();c=clean(s);ms=list(re.finditer(r'^(def|structure|inductive|abbrev|instance|opaque|axiom|theorem)\s+([^\s({:]+)',c,re.M));ds={}
 for i,m in enumerate(ms):
  b=c[m.start():ms[i+1].start() if i+1<len(ms) else len(c)];b=re.split(r'^end\b',b,flags=re.M)[0];b=re.sub(r'@\[[^\]]*\]','',b);b=' '.join(b.split())
  assert m[2] not in ds,(p,m[2])
  ds[m[2]]=dict(kind=m[1],line=s[:m.start()].count('\n')+1,sha256=sha(b.encode()),text=b)
 return ds
inv={k:inventory(p) for k,p in paths.items()};rows=[]
for typ in ['Types','Funs']:
 for n,a in inv['cohort_'+typ].items():
  rn=n.replace('aspis_core.field.WideExact','aspis_core.field.wide_exact.WideExact').replace('aspis_core.Digest32','aspis_core.digest.Digest32')
  found=next(((k,inv[k][rn]) for k in ['release_'+typ,'release_External'+typ] if rn in inv[k]),None)
  if found:
   k,b=found;status='external-template-only' if 'External' in k else 'same-normalized-text' if a['sha256']==b['sha256'] else 'different-normalized-text'
   (E/'XRi_diffs').mkdir(exist_ok=True)
   if status!='same-normalized-text':
    # One exact declaration pair per diff; namespace/path renames not normalized away.
    (E/'XRi_diffs'/('XRi_'+typ+'_'+n+'.diff')).write_text(''.join(difflib.unified_diff((a['text']+'\n').splitlines(True),(b['text']+'\n').splitlines(True),fromfile=paths['cohort_'+typ].as_posix()+':'+str(a['line']),tofile=paths[k].name+':'+str(b['line']))))
   rel=dict(file=paths[k].name,name=rn,**{q:v for q,v in b.items() if q!='text'})
  else:status='no-release-declaration';rel=None
  rows.append(dict(name=n,cohort_file=typ,cohort={q:v for q,v in a.items() if q!='text'},release=rel,status=status))
# Reuse the already completed adopted-top kernel reachability audit; no replay.
audit=R/'evidence/replay-dry9-20261027/RPz8_657/stdout.log';names=[]
for line in audit.read_text().splitlines():
 if 'RPZ8_REACHABLE_CONSTANTS ' in line:names=json.loads(line.split('RPZ8_REACHABLE_CONSTANTS ',1)[1])
assert names
prod={r['name']:r for r in rows};coverage=[]
for full in sorted(n for n in names if n.startswith('AspisR1PublicPreparation.')):
 n=full.removeprefix('AspisR1PublicPreparation.')
 candidates=[d for d in prod if n==d or n.startswith(d+'.')];d=max(candidates,key=len) if candidates else None
 coverage.append(dict(constant=full,producer_declaration=d,comparison_status=prod[d]['status'] if d else 'outside-selected-producer-pair: model/proof/other owner'))
used={r['producer_declaration'] for r in coverage if r['producer_declaration']}
for row in rows:row['reachable_from_adopted_top']=row['name'] in used
out=dict(qualification='Textual declaration comparison only, not elaboration or semantic association. Exact historical producer pair; root coverage reuses RPz8_657, not a new replay. Longest declaration prefix maps generated constructors/fields/helpers to their producer; outside-pair constants are explicitly retained.',normalization='Nested comments/attributes/whitespace removed; explicit name candidates WideExact -> field.wide_exact.WideExact and Digest32 -> digest.Digest32 only. Body text is not renamed for equality.',inputs={k:dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes()),bytes=p.stat().st_size,declarations=len(inv[k])) for k,p in paths.items()},audit=dict(path=str(audit.relative_to(R)),sha256=sha(audit.read_bytes()),all_reachable=len(names),public_preparation_constants=len(coverage),mapped_producer_declarations=len(used)),counts={s:sum(r['status']==s for r in rows) for s in sorted({r['status'] for r in rows})},reachable_counts={s:sum(r['status']==s and r['reachable_from_adopted_top'] for r in rows) for s in sorted({r['status'] for r in rows})},declarations=rows,coverage=coverage,generated_inventory={k:{n:{q:v for q,v in d.items() if q!='text'} for n,d in inv[k].items()} for k in inv if k.startswith('release_')})
(E/'XRi_declaration_diff.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['audit','counts','reachable_counts']},indent=2))
