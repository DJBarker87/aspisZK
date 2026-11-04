"""Fault-injection controls for the exact metadata-only lock-pin allowance."""
import copy,json
from pathlib import Path
import NEV_dot_aux as aux
E=Path(__file__).resolve().parent
original=aux.obj;passed=[]
def reject(name,path,mutate):
 def obj(p):
  result=original(p)
  if Path(p)==E/path:result=copy.deepcopy(result);mutate(result)
  return result
 aux.obj=obj
 try:
  aux.copies('NEV_K054','NEV_K055',['NEV_K050','NEV_K051'])
 except (AssertionError,ValueError,KeyError):passed.append(name)
 else:raise AssertionError('accepted '+name)
 finally:aux.obj=original
reject('extra non-lock pin rejected','NEV_K054/sources/NEV_SOURCE_PINS.json',lambda d:d.update({'unknown.rs':'0'*64}))
reject('changed frozen lock rejected','NEV_K054/sources/NEV_SOURCE_PINS.json',lambda d:d.update({'Cargo.lock':'0'*64}))
reject('changed existing source pin rejected','NEV_K054/sources/NEV_SOURCE_PINS.json',lambda d:d.update({'crates/aspis-core/src/field.rs':'0'*64}))
reject('changed Rust input receipt rejected','NEV_K050/receipt.json',lambda d:d['source_hashes'].update({'NEV_src/crates/aspis-core/src/field.rs':'0'*64}))
reject('different member features rejected','NEV_K050-graph-check.json',lambda d:d.update({'graph_matches_frozen':False}))
assert aux.run()['composed_rows_closed']==[]
(E/'NEV_DOT_AUX_TESTS.json').write_text(json.dumps(dict(passed=len(passed),controls=passed,no_slice_credit=True),indent=2)+'\n')
print(len(passed),'fault controls passed')
