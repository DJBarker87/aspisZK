from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin62-20261029';root=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';f=R/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean';ex=f.with_name('ProverRwFullExternalFuns.lean')
def clean(s):return re.sub(r'/\-.*?\-/|--[^\n]*','',s,flags=re.S)
def split(s):
 ms=list(re.finditer(r'^(?:def|abbrev) ([\w.]+)',s,re.M));return {m[1]:s[m.end():ms[i+1].start() if i+1<len(ms) else len(s)] for i,m in enumerate(ms)}
defs=split(clean(f.read_text()));fields={}
for m in re.finditer(r'^abbrev ([\w.]+).*? := @ExternalFuns\.op(\d+)',ex.read_text(),re.M):defs[m[1]]=' EXTOP'+m[2];fields[int(m[2])]=m[1]
defs['CAPTURE']=split(clean((root/'PV_RunJoin_NativeControl55.lean').read_text()))['run']
seen=set();q=['CAPTURE'];ops={};parents={'CAPTURE':None};token=re.compile(r'[\w]+(?:\.[\w]+)*')
while q:
 n=q.pop()
 if n in seen:continue
 seen.add(n)
 for o in re.findall(r'EXTOP(\d+)',defs[n]):ops.setdefault(int(o),[]).append(n)
 for t in token.findall(defs[n]):
  if t in defs and t not in seen:q.append(t);parents.setdefault(t,n)
# Read only the definitions which construct the historical dictionary.
selected=set();chains=[];pending=[('PV_RunJoin_WeightInstalled46','selected')];done=set()
while pending:
 mod,decl=pending.pop()
 if (mod,decl) in done:continue
 done.add((mod,decl));p=root/(mod+'.lean')
 if not p.exists():continue
 ss=clean(p.read_text());ms=list(re.finditer(r'^(?:@\[[^\n]*\]\s*)?(?:def|abbrev) ([\w.]+)',ss,re.M));body=None
 for i,m in enumerate(ms):
  if m[1]==decl:body=ss[m.end():ms[i+1].start() if i+1<len(ms) else len(ss)];body=re.split(r'\ntheorem |\n#print |\nattribute ',body)[0];break
 if body is None:continue
 selected.update(map(int,re.findall(r'\bop(\d+)\s*:=',body)));chains.append(dict(module=mod,declaration=decl,fields=sorted(map(int,re.findall(r'\bop(\d+)\s*:=',body)))))
 for md,dc in re.findall(r'([\w]+)\.(selected|install)\b',body):pending.append((md,dc))
 if mod=='ProverRwOuterTag' and decl=='selected':pending.append((mod,'install'))
ledger=(R/'design/PRIVACY-LEDGER-20261026.md').read_text();rowmap={int(m[2]):m[1] for m in re.finditer(r'^\| (V\d+) / `op(\d+) ',ledger,re.M)}
res=sorted(set(ops)-selected)
print('capture reachable',len(ops),'installed constructors',len(selected),'residual',res)
rows=[]
for n in res:
 path=[fields[n]];a=fields[n]
 while parents.get(a) is not None:a=parents[a];path.append(a)
 rows.append(dict(field='op'+str(n),number=n,name=fields[n],ledger_row=rowmap.get(n),reachability_path=list(reversed(path))))
out=dict(source_revision='474daaf0f1857fc01175426409f88c098716f659',dictionary_before='PV_RunJoin_WeightInstalled46.selected base heap box ops',capture_root='PV_RunJoin_NativeControl55.run capture',method='Syntactic declaration graph of the exact native prefix, with external aliases and trait dictionaries followed; conservative across branches, not an executable path solver. Callback parameters/store/hash are additional explicit inputs.',source_hashes={str(f.relative_to(R)):hashlib.sha256(f.read_bytes()).hexdigest(),str(ex.relative_to(R)):hashlib.sha256(ex.read_bytes()).hexdigest()},constructor_chain=chains,reachable_fields=sorted(ops),historically_installed_fields=sorted(selected),residual_fields=rows)
status=json.loads((E/'residual-status.json').read_text())
for row in out['residual_fields']:row.update(status['fields'][str(row['number'])])
for key in ['additional_publication_residuals','open_prefix_obligations','qualification']:out[key]=status[key]
(E/'residual-ops.json').write_text(json.dumps(out,indent=2)+'\n')
