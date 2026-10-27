from pathlib import Path
import re,json,hashlib,difflib,subprocess
B=Path(__file__).resolve().parent
R=B.parent.parent
paths={
 'cohort_Types': R/'docs/research/100bit-spend-path-20261013/lean/bridge-tx1-e5c186ba3-20261016/AspisR1PublicPreparation/Types.lean',
 'cohort_Funs': R/'docs/research/100bit-spend-path-20261013/lean-candidates/s1-prepared-claim-carrier-bridge-20261020/sources/AspisR1PublicPreparation/Funs.lean',
 'historical_Types':B/'XRb_historical_raw_Types.lean.txt','historical_Funs':B/'XRb_historical_raw_Funs.lean.txt',
 'diagnostic_Types':B/'XRb_DIAGNOSTIC_Types.lean.txt','diagnostic_Funs':B/'XRb_DIAGNOSTIC_Prepared_Funs.lean.txt'}
def digest(b):return hashlib.sha256(b).hexdigest()
def no_comments(s):
 # Generated Lean has nested block comments. Preserve line layout for locations.
 out=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;out.extend('  ');i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;out.extend('  ');i+=2
  elif depth:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s[i:i+2]=='--':
   k=s.find('\n',i);k=len(s) if k<0 else k;out.extend(' '*(k-i));i=k
  else:out.append(s[i]);i+=1
 return ''.join(out)
def declarations(p):
 s=p.read_text();clean=no_comments(s)
 ms=list(re.finditer(r'^(def|structure|inductive|abbrev|instance|opaque|axiom|theorem)\s+([^\s({:]+)',clean,re.M));out={}
 for i,m in enumerate(ms):
  body=clean[m.start():ms[i+1].start() if i+1<len(ms) else len(clean)]
  body=re.split(r'^end\b',body,flags=re.M)[0]
  body=re.sub(r'@\[[^\]]*\]','',body)
  norm=' '.join(body.split())
  out[m[2]]={'kind':m[1],'line':s[:m.start()].count('\n')+1,'normalized_sha256':digest(norm.encode()),'text':norm}
 return out
inv={k:{'path':str(p.relative_to(R)),'sha256':digest(p.read_bytes()),'bytes':p.stat().st_size,'declarations':declarations(p)} for k,p in paths.items()}
comparisons={}
for typ in ['Types','Funs']:
 for left,right in [(f'historical_{typ}',f'cohort_{typ}'),(f'diagnostic_{typ}',f'cohort_{typ}'),(f'diagnostic_{typ}',f'historical_{typ}')]:
  a=inv[left]['declarations'];b=inv[right]['declarations'];rows=[]
  for n in sorted(set(a)|set(b)):
   status='left_only' if n not in b else 'right_only' if n not in a else 'same_normalized_text' if a[n]['normalized_sha256']==b[n]['normalized_sha256'] else 'different_normalized_text'
   rows.append({'name':n,'status':status,'left':{k:v for k,v in a.get(n,{}).items() if k!='text'},'right':{k:v for k,v in b.get(n,{}).items() if k!='text'}})
  comparisons[left+'__'+right]={'qualification':'DIAGNOSTIC, incomplete body extraction; no equality proof' if left.startswith('diagnostic') else 'historical versus selected cohort; no release attribution','counts':{s:sum(r['status']==s for r in rows) for s in ['left_only','right_only','same_normalized_text','different_normalized_text']},'declarations':rows}
  diff=''.join(difflib.unified_diff(paths[left].read_text().splitlines(True),paths[right].read_text().splitlines(True),fromfile=left,tofile=right))
  (B/('XRb_'+left+'__'+right+'.diff')).write_text(diff)
(B/'XRb_declaration_diff.json').write_text(json.dumps({'exact_release_Types_Funs':'UNAVAILABLE: XRb_001 and 002 failed before emission','normalization':'remove comments, attributes, whitespace; compare same declared names only; no semantic-equivalence inference','inputs':{k:{**v,'declarations':{n:{kk:vv for kk,vv in d.items() if kk!='text'} for n,d in v['declarations'].items()}} for k,v in inv.items()},'comparisons':comparisons},indent=2)+'\n')
print(json.dumps({k:v['counts'] for k,v in comparisons.items()},indent=2))
# Quote exact release source blocks for each cut, with immutable revision provenance.
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
files={p:subprocess.check_output(['git','show',rev+':crates/aspis-r1-cost-probe/src/'+p]).decode() for p in ['verifier.rs','candidate.rs','fast_pairing.rs','r1_semantic.rs']}
selectors={'verify_observed':('r1_semantic.rs','pub fn verify_observed<'),'verifier_error':('verifier.rs','pub enum Error '),'dot_type':('fast_pairing.rs','pub struct Dot '),'prepared_new':('verifier.rs','pub fn new<H:Digest32>'),'prepared_claim':('verifier.rs','fn prepared_claim<'),'query_geometry':('verifier.rs','struct QueryGeometry '),'tx1':('candidate.rs','pub fn tx1<'),'tx1_finish_replacement_query_loop':('candidate.rs','fn query_loop(')}
for name,(p,needle) in selectors.items():
 s=files[p];i=s.index(needle);st=s.index('{',i);depth=1;e=st+1
 while depth:
  if s[e]=='{':depth+=1
  elif s[e]=='}':depth-=1
  e+=1
 (B/('XRb_release_'+name+'.rs.txt')).write_text(s[i:e])
