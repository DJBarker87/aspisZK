"""Fail-closed PCH graph validator. Re-read compiler evidence for edge completeness.
Usage on host: python3 PCH_VALIDATOR.py ATTEMPT [control].
Controls are graph/row mutations in memory; emitted evidence remains unchanged.
"""
import pathlib,json,lzma,re,hashlib,collections,sys,copy,shutil
B=pathlib.Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def load_graph():return json.loads(lzma.decompress((B/'PCH_GRAPH.json.xz').read_bytes()))
def compiler_lines(artifact):
 p=B/artifact
 if p.exists():return lzma.decompress(p.read_bytes()).decode().splitlines()
 # Reproduction from retained own host compiler output before client transfer.
 stem=artifact.removesuffix('.xz')
 if stem.startswith('PCH_B003_'):p=B/'PCH_B003'/stem.removeprefix('PCH_B003_')
 else:p=B/'PCH_B002'/stem.removeprefix('PCH_B002_')
 return p.read_text().splitlines()
def validate(g,v):
 assert g['elf_sha256']=='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc','ELF'
 assert len(v['rows'])==278 and len({r['row'] for r in v['rows']})==278,'278 rows retained'
 assert g['counts']['nodes']==len(g['nodes']) and g['counts']['edges']==len(g['edges']),'graph count mismatch'
 assert len({r['id'] for r in g['edges']})==len(g['edges']),'edge IDs'
 # Independent raw-artifact hashes and call/reference census; no golden verdict is accepted.
 lines={p:compiler_lines(p) for p in g['pins']}
 for p,pin in g['pins'].items():
  raw=('\n'.join(lines[p])+'\n').encode()
  assert sha(raw)==pin['uncompressed_sha256'],('compiler input drift',p)
 byloc=collections.defaultdict(list)
 for e in g['edges']:
  assert e['source'] in g['nodes'] and e['target'] in g['nodes'],('dangling',e['id'])
  byloc[(e['artifact'],e['line'])].append(e)
  if e['artifact'] in lines:
   text=lines[e['artifact']][e['line']-1]
   assert e['text_sha256'] in [sha(text.encode()),sha(text.strip().encode())],('edge text mismatch',e['id'])
 # MIR census does not rely on the producer's stored site list or counts.
 for p,ls in lines.items():
  if '.mir.' not in p:continue
  active=False
  for i,line in enumerate(ls,1):
   if line.startswith('fn '):active=True
   if not active:continue
   kind='MIR_INLINED_SCOPE' if '(inlined ' in line else ('MIR_DROP' if 'drop(' in line else 'MIR_CALL') if ' -> [' in line and (' = ' in line or 'drop(' in line) else 'MIR_FN_POINTER_OR_CLOSURE_MATERIALISATION' if any(t in line for t in ['ReifyFnPointer','ClosureFnPointer','PointerCoercion','closure@']) else None
   if kind:
    es=byloc[(p,i)];assert any(e['kind']==kind for e in es),('deleted MIR edge',p,i,kind)
    assert any(e['kind']==kind+'_UNRESOLVED' for e in es),('deleted unresolved MIR target',p,i)
 # LLVM completeness, including function materialisation and every vtable member.
 refpat=re.compile(r'@("(?:[^"\\]|\\.)+"|[-\w.$]+)')
 for p,ls in lines.items():
  if '.ll.' not in p:continue
  active=None
  for i,line in enumerate(ls,1):
   refs=refpat.findall(line)
   if line.startswith('define '):active='llvm:'+refs[0];continue
   if line.startswith('declare '):active=None;continue
   if line.startswith('@'):
    if not refs:continue
    kind='VTABLE_MATERIALISATION' if 'vtable' in refs[0] else 'GLOBAL_FUNCTION_REFERENCE'
    expected=refs[1:];source='global:'+refs[0]
   elif active:
    kind='LLVM_DIRECT_OR_INTRINSIC' if re.search(r'\b(call|invoke|callbr)\b',line) else 'LLVM_FUNCTION_OR_GLOBAL_MATERIALISATION';expected=refs;source=active
   else:continue
   for target in expected:
    key='llvm:'+target
    if key not in g['nodes'] and 'global:'+target in g['nodes']:key='global:'+target
    assert any(e['kind']==kind and e['source']==source and e['target']==key for e in byloc[(p,i)]),('deleted codegen edge',p,i,kind,target)
   if line=='}':active=None
 # Closure under universal indirect uncertainty and all required handler roots.
 universal={e['target'] for e in g['edges'] if e['source']=='PCH_UNKNOWN' and e['kind']=='UNRESOLVED_UNIVERSAL_TARGET'}
 assert universal=={k for k in g['nodes'] if k!='PCH_UNKNOWN' and not k.startswith('runtime-root:')},'deleted universal fn-pointer target'
 roots={r['instance'] for r in g['roots']};assert any('process_instruction' in k for k in roots),'processor root'
 for name in ['abort','__rust_alloc','__rust_dealloc','__rust_realloc','__rust_alloc_zeroed','__rust_alloc_error_handler']:assert 'runtime-root:'+name in roots,('handler root',name)
 for r in v['rows']:
  if r['verdict']=='EXCLUDED-CANDIDATE':
   assert r.get('codegen_cross_check',{}).get('absence_established') is True,('missing codegen exclusion cross-check',r['row'])
   assert r.get('caller_MIR_instances_resolved') is True,('unresolved exclusion',r['row'])
   assert not r.get('unresolved_witness'),('unresolved edge supports exclusion',r['row'])
   assert not r.get('resolved_codegen_witness'),('reachable row planted as exclusion',r['row'])
  elif r['verdict']=='UNRESOLVED':
   path=r.get('unresolved_witness');assert path,('no unresolved path',r['row'])
   edgebyid={e['id']:e for e in g['edges']} if 'edgebyid' not in locals() else edgebyid
   walk=[edgebyid[i] for i in path];assert walk[0]['source'] in roots and walk[-1]['target']=='row:'+r['row'],('bad path endpoints',r['row'])
   assert all(x['target']==y['source'] for x,y in zip(walk,walk[1:])),('broken witness',r['row'])
   assert any(not e['resolved'] for e in walk),('no unresolved edge',r['row'])
  else:assert False,('unsupported verdict',r['row'])
 return True

def main():
 a=sys.argv[1];control=sys.argv[2] if len(sys.argv)>2 else 'baseline';assert shutil.disk_usage(B).free>=40_000_000_000
 g=load_graph();v=json.loads((B/'PCH_VERDICTS.json').read_text());mutation=None
 if control=='planted_POOL_246':
  row=next(r for r in v['rows'] if r['row']=='POOL:246');assert row['inherited_status']=='CLOSED';row['verdict']='EXCLUDED-CANDIDATE';mutation=dict(row='POOL:246',kind='planted known CLOSED reachable row')
 elif control in ['deleted_real_call','deleted_fn_pointer','deleted_vtable']:
  kinds={'deleted_real_call':'LLVM_DIRECT_OR_INTRINSIC','deleted_fn_pointer':'LLVM_FUNCTION_OR_GLOBAL_MATERIALISATION','deleted_vtable':'VTABLE_MATERIALISATION'}
  candidate=next(e for e in g['edges'] if e['kind']==kinds[control] and (control!='deleted_fn_pointer' or g['nodes'][e['target']].get('definitions')))
  mutation=candidate.copy();g['edges']=[e for e in g['edges'] if e['id']!=candidate['id']]
  # Keep the superficial count consistent: failure must come from raw evidence completeness.
  g['counts']['edges']=len(g['edges'])
 elif control=='missing_codegen_check':
  row=v['rows'][0];row['verdict']='EXCLUDED-CANDIDATE';row.pop('codegen_cross_check',None);mutation=dict(row=row['row'],kind=control)
 try:validate(g,v);accepted=True;error=None
 except (AssertionError,KeyError,IndexError) as e:accepted=False;error=str(e)
 good=accepted if control=='baseline' else not accepted
 receipt=dict(attempt=a,control=control,validator_accepted=accepted,expected='ACCEPT' if control=='baseline' else 'REJECT',matched=good,diagnostic=error,mutation=mutation,graph_sha256=sha(lzma.decompress((B/'PCH_GRAPH.json.xz').read_bytes())),verdict_sha256=sha((B/'PCH_VERDICTS.json').read_bytes()),exit_status=0 if good else 1)
 (B/(a+'_VALIDATION.json')).write_text(json.dumps(receipt,indent=1)+'\n');print('PCH validator '+control+': '+('PASS' if good else 'FAIL'));sys.exit(0 if good else 1)
if __name__=='__main__':main()
