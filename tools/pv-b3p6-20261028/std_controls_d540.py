"""Small adversarial controls for the source-token audit; no proof/native runs."""
from pathlib import Path
import hashlib,json
p=Path('tools/pv-b3p6-20261028/std_resolve_d540.py');ns={};exec(compile(p.read_text().split('indices={}')[0],'<helpers>','exec'),ns)
index,tokens=ns['index'],ns['tokens'];checks=[]
def check(name,property):
 assert property,name
 checks.append(dict(name=name,passed=True))
check('comments and whitespace do not change lexical identity',tokens('fn f(){1 + 2}')==tokens('fn f( ) { /* fn fake(){} */ 1\n + 2 }'))
check('reordered short circuit operands must fail strict identity',tokens('{ ub_checks() && const_eval_select!(@capture {} -> bool: if const {false} else {!cfg!(miri)}) }')!=tokens('{ const_eval_select!(@capture {} -> bool: if const {false} else {!cfg!(miri)}) && ub_checks() }'))
check('string contents remain significant',tokens('{ "a // b" }')!=tokens('{ "a // c" }'))
s='impl<T, const N: usize> [T; N] { fn map<F>(self,f:F)->[T; N] { self } fn absent(&self); }'
rows=index(s);check('array-type semicolons do not hide a real function',[r['name']for r in rows]==['map'])
s='macro_rules! m { () => { fn forward_unchecked(start:Self,n:usize)->Self { unsafe { start.unchecked_add(n as Self) } } }; }'
rows=index(s);check('macro origin is retained',len(rows)==1 and rows[0]['macros']==['m'])
D=Path('evidence/pv-b3p6-20261028/resume17');x=json.loads((D/'K3-STD-PARITY-D540.json').read_text())
check('all captured generated runtime wrappers fail closed',all(r['status']=='COMPILER-GENERATED / UNRESOLVED' for r in x['rows']if '::runtime' in r['name']))
check('derived range Clone is a V370 item, never a body parity pass',all(r['status']=='COMPILER-GENERATED / UNRESOLVED' and 'V370'in r['classification']for r in x['rows']if r['name']=='<std::ops::Range<usize> as std::clone::Clone>::clone'))
check('a closure type argument does not turn its enclosing function into a compiler-generated item',all(r['classification']=='ordinary standard-library source item' for r in json.loads((D/'STD-PARITY-D540.json').read_text())['rows'] if r.get('kani_item',{}).get('name')=='try_map' and not r['name'].endswith('::{closure#0}')))
check('ordinary UB wrapper mismatch is retained',all(r['status']=='DIFFERENT' and r['classification']=='ordinary standard-library source item'for r in x['rows']if r['name']=='core::ub_checks::check_language_ub'))
(D/'STD-CONTROLS-D540.json').write_text(json.dumps(dict(method='adversarial source-parser controls; not Kani harnesses or proof runs',checks=checks,resolver_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),parser_packages={'tree-sitter':'0.25.2','tree-sitter-rust':'0.24.0'},charged_scopes=0),indent=2)+'\n')
print('PASS',len(checks),'adversarial audit controls')
