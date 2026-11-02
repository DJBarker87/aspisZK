"""Isolate pure original NDE contracts from unrelated log-writing modules."""
from NEK_priority import *
from NEK_recover import recover
import re

def prune(t,selected):
 statics=set(re.findall(r'\bstatic\s+mut\s+(\w+)',t))
 t=re.sub(r'^.*\bstatic\s+mut\b.*\n','',t,flags=re.M)
 lines=t.splitlines(True);out=[];i=0;pending=[]
 while i<len(lines):
  if lines[i].startswith('#['):pending.append(lines[i]);i+=1;continue
  if re.match(r'(?:pub(?:\([^)]*\))?\s+)?fn \w+',lines[i]):
   body=lines[i];i+=1;depth=body.count('{')-body.count('}')
   while depth>0 and i<len(lines):body+=lines[i];depth+=lines[i].count('{')-lines[i].count('}');i+=1
   if not any(re.search(r'\b'+n+r'\b',body) for n in statics) and 'NDE_field' not in ''.join(pending)+body and (not any('kani::proof' in a for a in pending) or re.search(r'fn '+selected+r'\s*\(',body)):out+=pending+[body]
   pending=[]
  else:out+=pending+[lines[i]];pending=[];i+=1
 result=''.join(out+pending)
 if not re.search(r'fn same_public[<(]',result):
  result=re.sub(r'pub\(super\) fn (?:private_matches|withdrawal_matches)\([^\n]*\n[^\n]*\n\}\n','',result)
 return result
def make(rp):
 o,missing=recover(rp)
 if missing:return None,'missing source'
 r=read_json(ROOT/rp);ni=r.get('native_command') or r['command'];h=r.get('module') or ni[ni.index('--harness')+1]
 if 'NDE_native::' not in h:return None,'not this shape'
 component=h.split('::NDE_native::')[0];function=h.rsplit('::',1)[1]
 path='crates/aspis-statement/src/'+component.replace('::','/')+'.rs'
 prefix=next((n[:-len(path)] for n in o if n.endswith(path)),None)
 if prefix is None:return None,'parent source not pinned'
 parent=o[prefix+path];mm=re.search(r'#\[path\s*=\s*"([^"]+)"\]\s*(?:pub(?:\([^)]*\))?\s+)?mod NDE_native',parent)
 if not mm:return None,'module path unresolved'
 mod=str(Path(path).parent/mm[1]);native=o.get(prefix+mod)
 if native is None:return None,'native module source missing'
 n=prune(native,function)
 if not re.search(r'fn '+function+r'\s*\(',n):return None,'selected function needs local-log migration'
 if 'static mut' in n:return None,'unmigrated storage'
 result=root('crates/aspis-statement','NDE_kmx','extern crate alloc;include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));')
 # Retain only the selected callee's contract attributes. Unselected proof
 # harnesses are omitted above, so no disabled contract is used as credit.
 selected_pos=n.index('fn '+function+'(')
 before=n[:selected_pos]
 match=list(re.finditer(r'kani::proof_for_contract\(super::(\w+)\)',before))
 target=match[-1][1] if match else None
 lines=parent.splitlines(True);filtered=[]
 for idx,line in enumerate(lines):
  if 'cfg_attr(kani' in line:
   rest=''.join(lines[idx+1:]);nextfn=re.search(r'\bfn\s+(\w+)\s*\(',rest)
   if not (target and nextfn and nextfn[1]==target):continue
  filtered.append(line)
 parent=''.join(filtered)
 if target:
  target_at=parent.index('fn '+target+'(')
  attrs=parent[max(0,parent.rfind('\n}',0,target_at)):target_at]
  assert 'kani::ensures' in attrs,('lost selected postcondition',rp,target)
 result[path]=parent;result[mod]=n
 # Exact recorded auxiliary pure reference modules; no arbitrary substitutions.
 for key,t in o.items():
  if key.startswith(prefix) and key.endswith('.rs'):
   suffix=key[len(prefix):]
   if Path(suffix).parent==Path(mod).parent and 'reference' in suffix.lower():result[suffix]=t
 core='crates/aspis-core/src/lib.rs';result[core]=frozen(core).decode()+'\n#[cfg(kani)] mod NEK_arbitrary;\n'
 result['crates/aspis-core/src/NEK_arbitrary.rs']='impl kani::Arbitrary for crate::field::M31{fn any()->Self{Self(kani::any())}}\nimpl kani::Arbitrary for crate::field::QM31{fn any()->Self{use crate::field::{M31,CM31};Self{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}}}\n'
 return result,'original pure contract, actual parent source and names; unselected writable-log functions omitted'
def run(start=99):
 A=read_json(ROOT/'evidence/k3-audit-20261030/NEH_APPLICABILITY.json');old=read_json(ROOT/'evidence/k3-audit-20261030/NEH_LEDGER_DELTA.json');st={r['receipt']:r['outcome'] for r in old['receipts']}
 todo=[];skips=[]
 for row in A['receipts']:
  rp=row['receipt']
  if 'native-front2-20261028/NDE_K' not in rp or st[rp]!='OPEN' or any(x in rp for x in ['K008/','K009/','K050/','K052/','K071/']):continue
  o,reason=make(rp)
  if o is None:skips.append(dict(receipt=rp,reason=reason));continue
  todo.append((rp,o,reason))
 (E/'NEK_NDE_PURE_PLAN.json').write_text(json.dumps(dict(selected=[dict(receipt=rp,method=reason) for rp,_,reason in todo],blocked=skips),indent=2)+'\n')
 if os.environ.get('NEK_PLAN_ONLY'):print(len(todo),'ready',len(skips),'blocked');return
 for i,(rp,o,reason) in enumerate(todo):
  a=f'NEK_K{start+i:03}'
  if (E/a/'receipt.json').exists():continue
  neg=read_json(ROOT/rp)['exit_status']!=0
  v=publish(a,rp,o,neg,reason)
  if 'error: could not compile' in (E/a/'stdout.log').read_text():raise SystemExit('own compile input error; inspect and repair')
if __name__=='__main__':run(int(sys.argv[1]) if len(sys.argv)>1 else 99)
