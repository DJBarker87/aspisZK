from pathlib import Path
import re,json,hashlib,difflib
E=Path(__file__).resolve().parent.parent
native=Path('crates/aspis-statement/src/state_only_poseidon.rs')
candidate=Path('docs/research/100bit-spend-path-20261013/evidence/terminal-indexed-source-candidate-20261017-explicit-low-folds/input/src/statement/state_only_poseidon.rs')
sha=lambda b:hashlib.sha256(b).hexdigest()
def declarations(path):
 s=path.read_text();masked=re.sub(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"',lambda m:' '*len(m[0]),s,flags=re.S)
 out={}
 for m in re.finditer(r'\bfn\s+(\w+)\s*[(<]',masked):
  name=m[1];a=masked.find('{',m.end());depth=1;b=a+1
  while depth:
   if masked[b]=='{':depth+=1
   if masked[b]=='}':depth-=1
   b+=1
  out[name]=dict(text=s[m.start():b],masked=masked[m.start():b],line=s[:m.start()].count('\n')+1)
 return s,out
ns,nd=declarations(native);cs,cd=declarations(candidate)
queue=['evaluate_state_only_poseidon_oracle_projected'];seen=set();rows=[]
while queue:
 name=queue.pop()
 if name in seen:continue
 seen.add(name);n=nd[name];c=cd.get(name)
 calls=set(re.findall(r'\b([A-Za-z_]\w*)\s*(?:::[^\n;]*?)?\(',n['masked']))
 queue += sorted((calls & nd.keys())-seen)
 row=dict(function=name,native_line=n['line'],native_sha256=sha(n['text'].encode()),candidate_present=c is not None)
 if c:
  row.update(candidate_line=c['line'],candidate_sha256=sha(c['text'].encode()),tokens_equal=re.sub(r'\s+','',n['masked'])==re.sub(r'\s+','',c['masked']))
  if not row['tokens_equal']:
   (E/'source-diffs').mkdir(exist_ok=True)
   (E/'source-diffs'/(name+'.diff')).write_text(''.join(difflib.unified_diff(c['text'].splitlines(True),n['text'].splitlines(True),fromfile='retained candidate',tofile='frozen native')))
 rows.append(row)
(E/'poseidon-source-audit.json').write_text(json.dumps(dict(native_path=str(native),native_sha256=sha(native.read_bytes()),candidate_path=str(candidate),candidate_sha256=sha(candidate.read_bytes()),reachable_local_functions=rows,note='Token comparison is a source inventory, not a semantic equivalence proof; external methods, constants and constructors require their own bindings.'),indent=2)+'\n')
print(json.dumps(dict(functions=len(rows),different=[r['function'] for r in rows if not r.get('tokens_equal')]),indent=2))
