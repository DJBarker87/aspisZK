"""Name every nonidentical reached item and every intrinsic/compiler boundary.
Only read frozen source captures; never use semantic equivalence as parity.
"""
from pathlib import Path
import json,re,hashlib,importlib.util
# Load only helpers, without regenerating reports as an import side effect.
helper=Path('tools/pv-b3p6-20261028/std_resolve_d540.py').read_text()
ns={};exec(compile(helper.split('indices={}')[0],'<std-resolver-helpers>','exec'),ns)
tokens=ns['tokens'];D=Path('evidence/pv-b3p6-20261028/resume17')
reports=[json.loads((D/n).read_text()) for n in ['STD-PARITY-D540.json','K3-STD-PARITY-D540.json']]
allrows=[r for x in reports for r in x['rows']];intrinsics=sorted({v for r in allrows for v in r.get('intrinsics',[])})
# Macros produce const_eval_select runtime functions, not direct Rust fn bodies.
if any('::runtime' in r['name'] for r in allrows):intrinsics.append('const_eval_select')
intrinsics=sorted(set(intrinsics));intrinsic_rows=[]
for name in intrinsics:
 row=dict(name='core::intrinsics::'+name,classification='V370 compiler-cohort item',owner=['D381','D386'],semantics='retained at existing compiler-cohort boundary; no source-law axiom installed',groups=sorted({r['group'] for r in allrows if name in r.get('intrinsics',[]) or name=='const_eval_select' and '::runtime' in r['name']}))
 for side in ['kani','deployed']:
  p=D/'std-sources/core/src/intrinsics/mod.rs';text=p.with_suffix(p.suffix+'.'+side).read_text()
  matches=list(re.finditer(r'\bfn\s+'+re.escape(name)+r'\b',text));assert len(matches)==1,(name,side,len(matches))
  m=matches[0];end=text.find(';',m.end());body=text.find('{',m.end())
  if body>=0 and (end<0 or body<end):
   depth=1;j=body+1
   while depth:depth+=(text[j]=='{')-(text[j]=='}');j+=1
   end=j
  else:end+=1
  row[side]=dict(file=str(p.with_suffix(p.suffix+'.'+side)),line=text.count('\n',0,m.start())+1,declaration=text[m.start():end],file_sha256=hashlib.sha256(text.encode()).hexdigest())
 row['declaration_tokens_identical']=tokens(row['kani']['declaration'])==tokens(row['deployed']['declaration'])
 intrinsic_rows.append(row)
items={}
for r in allrows:
 if r['status']=='IDENTICAL':continue
 key=(r['name'],r['source'],r['location'].get('line'),r['status'])
 if key not in items:
  items[key]=dict(name=r['name'],source=r['source'],kani_line=r['location'].get('line'),status=r['status'],classification=r['classification'],groups=[],symbols=[],kani_item=r.get('kani_item'),deployed_item=r.get('deployed_item'),note=('Generated source template is not its instantiated MIR; compiler-cohort item under V370, owner D381/D386.' if r['classification'].startswith('V370') else 'Strict source token identity not established; deployed credit withheld.'))
 v=items[key];v['groups']=sorted(set(v['groups']+[r['group']]));v['symbols']=sorted(set(v['symbols']+[r['symbol']]))
compiler=[]
# Add known compiler-replaced drop glue even when placeholder Rust tokens agree.
for r in allrows:
 if r.get('kani_item',{}).get('name')=='drop_in_place':
  compiler.append(dict(name=r['name'],source=r['source'],classification='V370 compiler-cohort item',owner=['D381','D386'],reason='rustc replaces recursive placeholder with actual drop glue',group=r['group']))
out=dict(target='V244 / runjoin op227 OPEN',source_identity_rule='k-double-prime; no relaxation',ordinary_or_generated_nonidentical_items=list(items.values()),intrinsic_items=intrinsic_rows,compiler_drop_glue=compiler,differing_source_declaration_names=sorted({r['kani_item']['name'] for r in allrows if r['status']=='DIFFERENT'}),budget_spent_in_this_audit=dict(lean=0,extraction=0,kani=0,std_scopes=0),endpoint_premise_changes=dict(removed=[],added=[],weakened=[]))
(D/'STD-ITEM-INVENTORY-D540.json').write_text(json.dumps(out,indent=2)+'\n')
lines=['# D540 strict std-parity items','', 'V244 and runjoin op227 remain OPEN. Every differing/absent item is named below; no semantic-equivalence substitution is used for k-double-prime. Intrinsic and compiler-lowering items remain **V370 compiler-cohort items (owner D381/D386)**. No endpoint premise is removed, added or weakened.','', 'Source reports: `STD-PARITY-D540.json`, `K3-STD-PARITY-D540.json`. Exact full names, monomorphisations, symbols, bodies, source lines and file hashes are in `STD-ITEM-INVENTORY-D540.json`. Previous reports are retained unchanged.','', '## All differing and absent source items','']
for v in items.values():
 if v['status'] not in ('DIFFERENT','ABSENT DEPLOYED DECLARATION'):continue
 lines += ['- `'+v['name']+'` — '+v['status']+'; groups '+', '.join(v['groups'])+'. '+v['classification']+'.']
lines+=['','## Compiler-generated items without established expansion parity','']
for v in items.values():
 if v['status'] not in ('DIFFERENT','ABSENT DEPLOYED DECLARATION'):lines+=['- `'+v['name']+'` — '+v['status']+'; groups '+', '.join(v['groups'])+'. '+v['classification']+'.']
lines+=['','## Intrinsics','', 'Every following item has a separately compared declaration. A matching declaration is not a proof of compiler semantics. Every one remains a V370 compiler-cohort item (owner D381/D386).','']
for r in intrinsic_rows:lines+=['- `'+r['name']+'` — declaration tokens '+('IDENTICAL' if r['declaration_tokens_identical'] else '**DIFFERENT**')+'.']
lines+=['','## Consequences','', '`check_language_ub` is an ordinary Rust function whose operands are reversed. Its called `ub_checks` intrinsic and `const_eval_select` lowering are distinct V370 items. The ordinary source mismatch still withholds credit; it is not relabelled as an intrinsic to evade k-double-prime.','', '`NeverShortCircuit::wrap_mut_1` now constructs `Wrapped { f, p: PhantomData }` instead of returning a closure. The enclosing ordinary function differs; each reached old closure is also explicitly a V370 lowering item. `ManuallyDrop::new`/`deref_mut`, array `try_map` and `Drain::drop` differ. Old slice `PartialEq::ne`, `SlicePartialEq::not_equal`, and old drain iterator methods/helper are absent at those origins.','', 'Step::forward_unchecked and TryFrom<usize> for isize now map to token-identical bodies in the same macro. The original regex skipped array-type semicolons and could not match macros or const-eligibility changes; this refinement does not alter body tokens. Derived Clone/PartialEq, FnMut call glue and const_eval_select runtime wrappers remain unestablished V370 items.','', 'Both mask copies and reconstruct retain their prior ordinary-source parity results. Transition, external/internal linear helpers and K73946/K73948 remain WITHHELD. No further sum gate was launched after the common mismatch. Strict parity failure does not disprove the application equality; it prevents this transfer route.','']
(D/'STD-ITEMS-D540.md').write_text('\n'.join(lines))
print(json.dumps(dict(nonidentical_items=len(items),intrinsics=len(intrinsic_rows),differing_intrinsic_declarations=[r['name'] for r in intrinsic_rows if not r['declaration_tokens_identical']],differing_source_declaration_names=out['differing_source_declaration_names'])))
