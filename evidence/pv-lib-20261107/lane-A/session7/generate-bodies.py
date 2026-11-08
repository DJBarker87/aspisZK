"""Render selected ALREADY EMITTED bodies with the unchanged pinned converter.
Syntax support only; conversion success is not native/source adequacy.
No cleanup is omitted and no unsupported case is converted by a guessed rule.
"""
from pathlib import Path
import ast,hashlib,json,lzma,subprocess,sys
E=Path('evidence/pv-lib-20261107/lane-A/session7');R='3eae57e2a2cdf6be5eb06ab8b45e7df7c5bf1404'
check='--check'in sys.argv
sha=lambda b:hashlib.sha256(b).hexdigest()
def functions(s):return ast.Module(body=[n for n in ast.parse(s).body if isinstance(n,ast.FunctionDef)],type_ignores=[])
helpers=[];sources={}
for n in ['generate-intermediate-d685.py','generate-slice.py']:
 p='tools/pv-stx-20261104/'+n;b=subprocess.check_output(['git','show',R+':'+p]);q=E/(n+'.txt')
 if check:assert q.read_bytes()==b
 else:q.write_bytes(b)
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
raw=lzma.decompress((E/'NativeInstructions.json.xz').read_bytes());p=json.loads(raw)
assert sha(raw)=='fe0cbaedf427d3fdd1cd5e3dc8171728e82282d2f98b000f5a15d1cd37210a03'
rows=[]
for fid in [486,584,608,214,168,122,128,454,14,4]:
 f=next(f for f in p['functions']if f['function']==fid);code=f['code'];r=dict(function=fid,code_sha256=sha(json.dumps(code,separators=(',',':')).encode()))
 if 'body'not in code:r.update(status='OPAQUE; no program invented');rows.append(r);continue
 conv['parts']=[];failures.clear()
 try:body=conv['block'](code['body'])
 except (KeyError,AssertionError)as err:r.update(status='CONVERSION GAP; no cleanup omitted',error=repr(err),failed_instructions=list(failures));rows.append(r);continue
 module='PV_LIB_A_Emitted'+str(fid);decls=['def '+n+' : '+t+' :=\n  '+v for n,t,v in conv['parts']]
 text='\n'.join(['import PV_STX2_SliceSyntax','set_option autoImplicit false','namespace '+module,'open PV_STX2_Syntax PV_STX2_SliceSyntax','/- Exact retained N95808 syntax, converted with unchanged pinned helpers. Syntax only. -/',*decls,'def program : PV_STX2_SliceSyntax.Program :=\n  ⟨'+str(fid)+', '+conv['data'](code['entry'])+', '+conv['data'](code['locals'])+', '+body+'⟩','#print axioms program','end '+module,''])
 q=Path('lean',module+'.lean')
 if check:assert q.read_text()==text
 else:q.write_text(text)
 r.update(status='GENERATED SYNTAX ONLY',module=module,source=str(q),sha256=sha(text.encode()),bytes=len(text.encode()));rows.append(r)
result=dict(emission_sha256=sha(raw),pinned_conversion_helpers=helpers,functions=rows,qualification=__doc__)
q=E/'EMITTED_BODIES.json'
if check:assert json.loads(q.read_text())==result
else:q.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps([dict(function=r['function'],status=r['status'],error=r.get('error'),bytes=r.get('bytes'))for r in rows],indent=2))
