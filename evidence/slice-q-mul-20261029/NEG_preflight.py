from pathlib import Path
import subprocess,hashlib,json,re
E=Path(__file__).resolve().parent
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
names={'crates/aspis-r1-cost-probe/src/fast_dots.rs':['four_dots_one'],'crates/aspis-r1-cost-probe/src/verifier.rs':['update_residue_row','batch_prefix_products','circle_fold_with_inverses','line_fold_with_inverses','accumulate_batched_with_node']}
def body(s,name):
 m=re.search(r'\bfn '+name+r'\b',s); assert m,name
 start=s.index('{',m.start());depth=1;i=start+1
 while depth:
  if s[i]=='{':depth+=1
  elif s[i]=='}':depth-=1
  i+=1
 return s[m.start():i]
r={}
for path,functions in names.items():
 frozen=subprocess.check_output(['git','show',F+':'+path],text=True);current=Path(path).read_text();assert current==frozen
 for name in functions:
  b=body(frozen,name)
  r[name]=dict(path=path,sha256=hashlib.sha256(b.encode()).hexdigest(),mutable_iterator_candidate=bool(re.search(r'for\s+limb\s+in\s+row',b)),inline_product_lines=[l.strip() for l in b.splitlines() if re.search(r'\s\*\s|\)\*',l)],calls=[x for x in re.findall(r'\b(\w+)\(',b) if x not in ['fn',name]])
(E/'NEG_STATIC_SCAN.json').write_text(json.dumps(dict(frozen_revision=F,scan_kind='conservative source scan; not a proof of translator fidelity',functions=r),indent=2)+'\n')
print(json.dumps(r,indent=2))
