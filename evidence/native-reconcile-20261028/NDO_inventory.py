"""Inventory source closure names; no compilation or object mutation."""
import json,lzma,re,hashlib,subprocess,collections,difflib
from pathlib import Path
E=Path(__file__).resolve().parent
pins=json.loads(lzma.open(E.parent/'native-l188-20261028/NDJ_CACHE_PINS.json.xz','rt').read())
u={r['module']:r for r in pins['objects'] if r['selection']=='union'}
j={r['module']:r for r in pins['objects'] if r['selection']=='joint'}
h=set()
def walk(m):
 if m in h:return
 h.add(m)
 for n in u[m]['imports']:walk(n)
walk('RPx_Deployed')
files=subprocess.check_output(['git','ls-files','*.lean'],text=True).splitlines();by=collections.defaultdict(list)
for f in files:by[Path(f).stem].append(f)
# Replay flattening maps dotted historical modules to underscored basenames.
canon={m.replace('.','_'):m for m in j}
pairs=sorted((canon[k],m) for m in h if m.startswith('RP') and (k:=re.sub(r'^RP[^_]*_','',m)) in canon)
selected={a:b for a,b in pairs}
def source(m,replay=False):
 exact='lean/'+m.replace('.','/')+'.lean'
 if not replay:
  choices=[f for f in files if f.endswith('/'+m.replace('.','/')+'.lean') or f==exact]
  if choices:return min(choices,key=len)
 opts=by[m.replace('.','_')]
 opts=[p for p in opts if '/sources/' not in p] or opts
 opts.sort(key=lambda p:(not p.startswith('evidence/replay-'),len(p),p))
 if not opts:raise ValueError('missing '+m)
 return opts[0]
paths={m:source(m,m in h and m.startswith('RP')) for pair in pairs for m in pair}
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
def read(path):
 proc.stdin.write(('HEAD:'+path+'\n').encode());proc.stdin.flush();header=proc.stdout.readline().split();n=int(header[-1]);b=proc.stdout.read(n);proc.stdout.read(1);return b
raw={m:read(p) for m,p in paths.items()};proc.stdin.close();proc.wait()
for m in ['Op5T_Final','Op5T_SuccessAccepted']:
 paths[m]=str(E/('NDO_'+m+'.original.lean.txt'));raw[m]=Path(paths[m]).read_bytes()
def normal(b):
 s=b.decode()
 def fix(mt):
  return 'import '+' '.join(selected.get(n,n) for n in mt.group(1).split())
 return re.sub(r'^import\s+([^\n]+)',fix,s,flags=re.M).encode()
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[];diff=[]
for old,new in pairs:
 a,b=raw[old],raw[new];norm=normal(a);same=norm==b
 # A second, explicitly weaker comparison ignores comments/whitespace/imports.
 def body(x):return re.sub(r'\s+',' ',re.sub(r'^import[^\n]*\n','',re.sub(r'/\-.*?\-/|--[^\n]*','',x.decode(),flags=re.S),flags=re.M)).strip()
 row=dict(historical=old,replay=new,historical_source=paths[old],replay_source=paths[new],historical_sha256=sha(a),replay_sha256=sha(b),identical_after_module_import_rename=same,body_equal_ignoring_comments_whitespace_imports=body(a)==body(b),historical_object_sha256=j[old]['sha256'],replay_object_sha256=u[new]['sha256'])
 if not same:diff.extend(['\n### '+old+' -> '+new+'\n',*difflib.unified_diff(norm.decode().splitlines(True),b.decode().splitlines(True),fromfile=paths[old],tofile=paths[new],n=2)])
 rows.append(row)
for row in rows:
 if row['identical_after_module_import_rename']:why='Exact bytes agree after complete import-module token replacement.'
 elif row['body_equal_ignoring_comments_whitespace_imports']:why='Comments/whitespace differ; full diff retained; no non-import code difference detected.'
 elif row['historical']=='S1SemanticPhaseV1':why='Historical verifier.Phase abbreviation is removed; replay retains exactly FirstCaller.Phase as RPz7_PhaseIso.Phase. NDO_L006 checks retainedCarrier without axioms. The emitted verifier.Phase remains a distinct nominal carrier.'
 elif row['historical']=='FIr_FinishComparison':why='Replay explicitly applies observerToFirst at the FinishModel hypothesis and proof call; this is callback transport, not mere import renaming. Existing PhaseIso round trips are reused and checked by NDO_L006; whole execution equivalence is not inferred.'
 else:why='Observer carrier annotation changes from the historical verifier.Phase alias to RPz7_PhaseIso.Phase. Both historical/replay aliases denote FirstCaller.Phase (NDO_L006 retainedCarrier). This does not identify the emitted producer verifier.Phase or prove all consumer transports; NDO_L002 demonstrates an unchanged witness consumer is ill-typed.'
 row['difference_analysis']=why
rows.sort(key=lambda r:r['identical_after_module_import_rename'])
provenance=json.loads((E/'NDO_PREDECESSOR_SOURCE_PINS.json').read_text())
for row in rows:
 row['historical_producer_provenance']=provenance.get(row['historical'],{})
 for v in row['historical_producer_provenance'].values():assert v['sha256']==row['historical_sha256'],row['historical']
(E/'NDO_DUPLICATES.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),method='Exact git source bytes; rewrite only complete import module tokens using closure pair mapping. Nonidentical pairs first. Object hashes are predecessor selections; source provenance is separately stated.',headline_count=len(h),joint_count=len(j),pair_count=len(rows),nonidentical_count=sum(not r['identical_after_module_import_rename'] for r in rows),pairs=rows),indent=2)+'\n')
(E/'NDO_SOURCE_DIFFS.txt').write_text(''.join(diff))
(E/'NDO_NAME_MAP.json').write_text(json.dumps(selected,indent=2)+'\n')
print('pairs',len(rows),'nonidentical',sum(not r['identical_after_module_import_rename'] for r in rows),'body differences',sum(not r['body_equal_ignoring_comments_whitespace_imports'] for r in rows))
