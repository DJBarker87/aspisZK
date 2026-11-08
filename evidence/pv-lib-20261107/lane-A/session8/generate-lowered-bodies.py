"""Render retained bodies, lowering cleanup Match with checked variant keys.
Syntax support only; conversion success is not native/source adequacy.
No cleanup is omitted and no unsupported case is converted by a guessed rule.
"""
from pathlib import Path
import ast,hashlib,json,lzma,subprocess,sys
E=Path('evidence/pv-lib-20261107/lane-A/session8');R='3eae57e2a2cdf6be5eb06ab8b45e7df7c5bf1404'
check='--check'in sys.argv
sha=lambda b:hashlib.sha256(b).hexdigest()
def functions(s):return ast.Module(body=[n for n in ast.parse(s).body if isinstance(n,ast.FunctionDef)],type_ignores=[])
helpers=[];sources={}
for n in ['generate-intermediate-d685.py','generate-slice.py']:
 p='tools/pv-stx-20261104/'+n;b=subprocess.check_output(['git','show',R+':'+p]);q=E.parent/'session7'/(n+'.txt')
 if check:assert q.read_bytes()==b
 else:assert q.read_bytes()==b
 sources[n]=b.decode();helpers.append(dict(revision=R,path=p,retained=str(q),sha256=sha(b)))
ns=dict(json=json);exec(compile(functions(sources['generate-intermediate-d685.py']),'pinned-helper-functions','exec'),ns)
failures=[]
original_instruction=ns['instruction']
def checked_instruction(statement):
 try:return original_instruction(statement)
 except (KeyError,AssertionError) as error:
  failures.append(dict(identity=statement.get('identity'),native_opcode=statement.get('native_opcode'),native=statement.get('native'),error=repr(error)))
  raise
ns['instruction']=checked_instruction
conv=dict(ns=ns,parts=[],json=json);conv.update({n:ns[n]for n in ['data','arg','place','operand','site']});exec(compile(functions(sources['generate-slice.py']),'pinned-node-functions','exec'),conv)

llbc=json.loads(lzma.decompress((E.parent/'session5/thread-llbc.json.xz').read_bytes()))['translated'];dictionary={}
def collect(x):
 if isinstance(x,dict):
  if 'HashConsedValue'in x:i,v=x['HashConsedValue'];dictionary[i]=v
  for v in x.values():collect(v)
 elif isinstance(x,list):
  for v in x:collect(v)
collect(llbc)
def normal(x):
 if isinstance(x,dict):
  if 'HashConsedValue'in x:return normal(x['HashConsedValue'][1])
  if 'Deduplicated'in x:return normal(dictionary[x['Deduplicated']])
  return {k:normal(v) for k,v in x.items()}
 if isinstance(x,list):return list(map(normal,x))
 return x
original_data=ns['data'];arity=0
used=set()
def typed_data(x):
 x=normal(x)
 if isinstance(x,dict) and list(x)==['TypeVar'] and 'Free' in x['TypeVar']:
  v=x['TypeVar'];assert list(v)==['Free'];i=v['Free'];assert i<arity;used.add(i)
  return '(types['+str(i)+']?.getD .null)'
 if isinstance(x,list):return '.array ['+', '.join('('+typed_data(v)+')' for v in x)+']'
 if isinstance(x,dict):return '.object ['+', '.join('('+json.dumps(k)+', ('+typed_data(v)+'))' for k,v in x.items())+']'
 return original_data(x)
ns['data']=typed_data;conv['data']=typed_data


# The original converter is unchanged for every instruction except Match.
# A cleanup Match uses the same read via Copy and the proved private switch keys.
previous_instruction=ns['instruction'];lowered_matches=[]
def lower_instruction(s):
 n=s['native']
 if isinstance(n,dict) and 'Switch'in n and 'Match'in n['Switch']:
  p,arms,other=n['Switch']['Match'];t=ns['site'](s)
  gap='.bind '+t+' (.local 0) (.nullary (.object [("PV_LIB_A_MatchGap",.boolean true)]))'
  rendered=['([(.object [("PV_LIB_A_MatchInvalid",.boolean true)])], ['+gap+'])']
  for keys,body in arms:
   ks=['(.object [("PV_LIB_A_MatchVariant",.number '+str(k)+')])'for k in keys]
   rendered.append('(['+', '.join(ks)+'], '+ns['block'](body)+')')
  default='['+gap+']'if other is None else ns['block'](other)
  lowered_matches.append(dict(identity=s['identity'],variants=[keys for keys,_ in arms],has_otherwise=other is not None))
  return '.switch '+t+' (.copy '+ns['arg'](ns['place'](p))+') ['+', '.join(rendered)+'] '+default
 return previous_instruction(s)
ns['instruction']=lower_instruction

raw=lzma.decompress((E.parent/'session7/NativeInstructions.json.xz').read_bytes());p=json.loads(raw)
assert all(tag.encode() not in raw for tag in ['PV_LIB_A_MatchGap','PV_LIB_A_MatchInvalid','PV_LIB_A_MatchVariant'])
assert sha(raw)=='fe0cbaedf427d3fdd1cd5e3dc8171728e82282d2f98b000f5a15d1cd37210a03'
rows=[]
for fid in [644,454]:
 f=next(f for f in p['functions']if f['function']==fid);code=f['code'];arity=len(llbc['fun_decls'][fid]['generics']['types']);used.clear();r=dict(function=fid,code_sha256=sha(json.dumps(code,separators=(',',':')).encode()))
 if 'body'not in code:r.update(status='OPAQUE; no program invented');rows.append(r);continue
 conv['parts']=[];failures.clear();lowered_matches.clear()
 try:body=conv['block'](code['body'])
 except (KeyError,AssertionError)as err:r.update(status='CONVERSION GAP; no cleanup omitted',error=repr(err),failed_instructions=list(failures));rows.append(r);continue
 module='PV_LIB_A_LoweredBody'+str(fid);names={n for n,t,v in conv['parts']}
 def parameterize(v):
  import re
  return re.sub(r'\b(?:node|block)[0-9]+\b',lambda m:'('+m[0]+' types)',v)
 decls=['def '+n+' (types : List Data) : '+t+' :=\n  '+parameterize(v) for n,t,v in conv['parts']]
 text='\n'.join(['import PV_LIB_A_TypedDestruct'
,'import PV_STX2_SliceSyntax'
,'import PV_LIB_A_UnwindMatch','set_option autoImplicit false','namespace '+module,'open PV_STX2_Syntax PV_STX2_SliceSyntax','/- Exact retained N95808 syntax, converted with unchanged pinned helpers. Syntax only. -/',*decls,'def program (types : List Data) : PV_STX2_SliceSyntax.Program :=\n  ⟨'+str(fid)+', '+conv['data'](code['entry'])+', '+conv['data'](code['locals'])+', ('+body+' types)⟩',
 'def instantiate (types : List Data) : Option PV_STX2_SliceSyntax.Program :=\n  if types.length = '+str(arity)+' then some (program types) else none',
 '#print axioms instantiate','#print axioms program','end '+module,''])
 q=Path('lean',module+'.lean')
 if check:assert q.read_text()==text
 else:q.write_text(text)
 r.update(lowered_matches=list(lowered_matches),required_carrier='PV_LIB_A_UnwindMatch.carrier C K',status='GENERATED LOWERED SYNTAX ONLY; selection proof is UnwindMatchCorrectness.selection',module=module,source=str(q),sha256=sha(text.encode()),bytes=len(text.encode()));rows.append(r)
result=dict(emission_sha256=sha(raw),pinned_conversion_helpers=helpers,functions=rows,qualification=__doc__)
q=E/'LOWERED_BODIES.json'
if check:assert json.loads(q.read_text())==result
else:q.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps([dict(function=r['function'],status=r['status'],error=r.get('error'),bytes=r.get('bytes'))for r in rows],indent=2))
