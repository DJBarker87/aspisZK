"""Compare raw Lean Expr representations modulo explicit matcher renaming/alpha.

This is a structural expression audit, not a new Lean theorem. It compares all
references and helper definitions, not only hashes or printed theorem types.
"""
from pathlib import Path
import json,hashlib,re,sys
B=Path(sys.argv[1]);which=sys.argv[2]
rename={}
for ns in ['AspisR1RecordParser','AspisR1PrefixAggregateParser']:
 p=ns+'.r1_wire.'
 rename[p+'Error.Insts.CoreFmtDebug.fmt.match_1']=p+'Error.Insts.CoreCmpPartialEqError.eq.match_1'
 for s in ['parse_record','validate_record_fields_loop.body']+(['Prefix.parse'] if 'PrefixAggregate' in ns else []):
  rename[p+s+'.match_3']=p+s+'.match_2'
def canon_repr(s):
 # Parentheses/lists and strings form the complete retained Expr repr grammar.
 tokens=re.findall(r'"(?:\\.|[^"\\])*"|[()\[\],]|[^\s()\[\],]+',s)
 pos=0
 def parse(end=None):
  nonlocal pos
  out=[]
  while pos<len(tokens):
   t=tokens[pos];pos+=1
   if t==end:return out
   if t in ['(', '[']:
    out.append(parse(')' if t=='(' else ']'))
   else:
    assert t not in [')',']'],t
    if t!=',':out.append(t)
  assert end is None,'unterminated repr'
  return out
 tree=parse();assert pos==len(tokens)
 def norm(x):
  if isinstance(x,str):
   return '`'+rename.get(x[1:],x[1:]) if x.startswith('`') else x
  x=[norm(y) for y in x]
  if x and x[0] in ['Lean.Expr.lam','Lean.Expr.forallE','Lean.Expr.letE']:
   x[1]='ALPHA_BINDER'
  # Metadata is deliberately not erased; unexpected metadata changes fail.
  return x
 return norm(tree)
def sha(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def canonical(row):
 return {k:(canon_repr(v) if k in ['type','value'] else rename.get(v,v) if k=='name' else sorted(rename.get(n,n) for n in v) if k=='refs' else v) for k,v in row.items()}
before_file=B/f'DFm_{which}-before.json';after_file=B/f'DFm_{which}-after.json'
a=json.loads(before_file.read_text());z=json.loads(after_file.read_text())
old={x['name']:x for x in a};new={x['name']:x for x in z}
ca={rename.get(n,n):canonical(x) for n,x in old.items() if '.CoreFmtDebug' not in n or n in rename}
cz={n:canonical(x) for n,x in new.items()}
changes=[];retained=[]
for n in sorted(ca.keys()&cz.keys()):
 fields=[k for k in ca[n] if ca[n][k]!=cz[n][k]]
 if fields:changes.append(dict(name=n,fields=fields))
 retained.append(dict(name=n,before_canonical_sha256=sha(ca[n]),after_canonical_sha256=sha(cz[n]),equal=not fields))
remaining_nonstandard=[dict(name=x['name'],axioms=x['axioms']) for x in z if set(x['axioms'])-{'propext','Classical.choice','Quot.sound'}]
x=dict(method='Exact Expr repr token-tree comparison; binder names erased only; explicit bijection of seven compiler-generated helper names, including their bodies; no metadata erasure, reduction, or axioms added',before_count=len(a),after_count=len(z),renaming=rename,raw_removed=sorted(old.keys()-new.keys()),raw_added=sorted(new.keys()-old.keys()),canonical_removed=sorted(ca.keys()-cz.keys()),canonical_added=sorted(cz.keys()-ca.keys()),canonical_changes=changes,all_retained_equal=not changes and ca.keys()==cz.keys(),retained=retained,nonstandard_after=remaining_nonstandard,before_sha256=hashlib.sha256(before_file.read_bytes()).hexdigest(),after_sha256=hashlib.sha256(after_file.read_bytes()).hexdigest(),snapshot_sizes=[before_file.stat().st_size,after_file.stat().st_size])
(B/f'DFm_{which}-semantic-comparison.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({k:v for k,v in x.items() if k not in ['retained','raw_removed','renaming']}))
