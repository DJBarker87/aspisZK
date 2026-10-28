from pathlib import Path
import re,json,lzma,hashlib,collections,sys
D=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');S=D/'src';mode=sys.argv[1] if len(sys.argv)>1 else 'historical';O=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028/typed-reached');O.mkdir(exist_ok=True)
# Reuse exactly the normalizers already audited, without running their comparison drivers.
a={};exec((D/'compare.py').read_text().split('maps={};')[0],a);b={};exec((D/'library-compare.py').read_text().split('variants=')[0],b)
def own(p):
 text=p.read_text();out={}
 for m in re.finditer(r'^fn ([^\n]+)\{\n.*?^}\n',text,re.M|re.S):
  v=a['normalize'](m[0]);key=v.split('\n')[0][3:].removesuffix(' {').strip()
  if 'MIR FOR CTFE' in text[max(0,m.start()-60):m.start()]:key+=' [CTFE]'
  assert key not in out;out[key]=v
 return out
libfiles=json.loads((D/'library-comparison/library-mir-manifest.json').read_text());nodes={};metadata={}
for cohort,oc,lc in [('old','charon','charon'),('deployed','ct','client194-exact')]:
 if mode=='features' and cohort=='old':oc='feature-control';lc='client194-exact'
 n={}
 for crate,prefix in [('aspis_core','core'),('aspis_statement','statement'),('aspis_r1_cost_probe','probe')]:
  for k,v in own(D/(({'core':'core-ct-release','statement':'statement-optimized2-release','probe':'probe-optimized-release'}[prefix]) if oc=='feature-control' else prefix+'-'+oc+'-release')/'crate.mir').items():n[crate+'::'+k]=v
 for item in libfiles:
  if item['variant']!='libraries-'+lc:continue
  lib=item['library']
  for k,v in b['parse'](D/('libraries-'+lc)/item['file']).items():n[lib+'::'+k]=v
 nodes[cohort]=n
# Names and receiver candidates are resolved from MIR symbols, not a source regex call inventory.
def name_info(k):
 arg=re.search(r'\((?=_\d+:|\))',k);prefix=k[:arg.start()] if arg else k
 method=prefix.split('::')[-1];impls=re.findall(r'(?:<|::)impl(.*?)(?=>::)',prefix)
 typ=[]
 for imp in impls:
  if ' for ' in imp:imp=imp.split(' for ')[-1]
  else:imp=re.sub(r'^<.*?>\s*','',imp).strip()
  t=re.search(r'\b([A-Z][A-Za-z0-9_]*|u8|u32|u64|usize|str)\b',imp)
  if t:typ.append(t[1])
 if not typ:
  # Derives and opaque source locations still expose their receiver in argument/result types.
  if '::<impl at ' in prefix:
   m=re.search(r'_1: &(?:mut )?([A-Z]\w*)',k)
   if m:typ.append(m[1])
 return method,typ
indexes={}
for cohort,ns in nodes.items():
 ix=collections.defaultdict(list)
 for k in ns:
  m,t=name_info(k)
  if '[CTFE]' not in k:ix[m].append((k,t))
 indexes[cohort]=ix

def split_call(s):
 dep=0
 for i,c in enumerate(s):
  if c=='<':dep+=1
  elif c=='>':dep=max(0,dep-1)
  elif c=='(' and dep==0:return s[:i].strip()
 return None
primitive={'drop','copy_nonoverlapping','copy','write_bytes','volatile_load','volatile_store','transmute','size_of','min_align_of','unreachable','abort','black_box','assume','discriminant_value','arith_offset','offset','ptr_offset_from','ptr_offset_from_unsigned','likely','unlikely','cold_path','caller_location','assert_inhabited','assert_zero_valid','assert_mem_uninitialized_valid','forget','drop_in_place'}
typed_decisions=[]
cache={}
def edges(cohort,key):
 c=(cohort,key)
 if c in cache:return cache[c]
 ns=nodes[cohort];ix=indexes[cohort];resolved=set();unknown=[]
 for line in ns[key].splitlines():
  if ' -> [return:' not in line and ' -> unwind ' not in line:continue
  expr=line.strip().split(' = ',1)[-1];call=split_call(expr)
  if not call:continue
  # Remove generic parameters solely for symbol matching, retaining the original in unresolved output.
  stripped=call
  while re.search(r'<[^<>]*>',stripped):stripped=re.sub(r'<[^<>]*>','',stripped)
  method=stripped.rstrip(':').split('::')[-1]
  if re.match(r'^<[A-Z] as ',call) or re.match(r'^[A-Z]::',call):
   continue # Explicit generic dictionary/closure argument, compared parametrically at this source-law boundary.
  if re.fullmatch(r'<(?:u8|u16|u32|u64|usize|i32|i64) as From<(?:u8|u16|u32)>>::from',call):continue
  if '{closure@' in call:
   span=re.search(r'\{closure@([^}]+)\}',call)[1];cs=[k for k in ns if '{closure@'+span+'}' in k]
   if len(cs)==1:resolved.add(cs[0]);continue
  if re.fullmatch(r'_\d+',method):unknown.append(dict(call=call,reason='indirect function/dictionary callback'));continue
  if method in primitive:continue
  typed=None
  if re.fullmatch(r'<Option<.+> as FromResidual<Option<Infallible>>>::from_residual',call):
   typed=[k for k,t in ix.get(method,[]) if '(_1: Option<Infallible>) -> Option<T>' in k]
  elif re.fullmatch(r'<Result<.+> as FromResidual<Result<Infallible, .+>>>::from_residual',call):
   typed=[k for k,t in ix.get(method,[]) if '(_1: result::Result<Infallible, E>) -> result::Result<T, F>' in k]
  elif re.fullmatch(r'<\[u8\] as Index<core::ops::Range<usize>>>::index',call):
   typed=[k for k,t in ix.get(method,[]) if k.startswith('core::slice::index::') and '(_1: &[T], _2: I)' in k]
  elif re.fullmatch(r'<\[u8; 32\] as PartialEq>::eq',call):
   typed=[k for k,t in ix.get(method,[]) if 'array/equality.rs' in k and '(_1: &[T; N], _2: &[U; N])' in k]
  if typed is not None:
   assert len(typed)==1,(cohort,call,typed)
   resolved.add(typed[0]);typed_decisions.append(dict(cohort=cohort,caller=key,call=call,target=typed[0],basis='Full input/return carrier and trait residual types; no method-name-only choice'));continue
  candidates=ix.get(method,[])
  # A free callee name cannot denote an inherent method with the same spelling.
  if '::' not in call:
   free=[(k,t) for k,t in candidates if '::< ' not in k and '::<impl' not in k and '::impl ' not in k]
   if free:candidates=free
  # Match the concrete receiver against the outer argument/return carrier; never use a nested type as the receiver.
  receiver=None
  if call.startswith('<') and ' as ' in call:
   lhs=call[1:].split(' as ',1)[0];mr=re.search(r'(?:^|::)([A-Z][A-Za-z0-9_]*|u8|u32|u64|usize)(?:<|$)',lhs)
   if mr:receiver=mr[1]
  else:
   mr=re.search(r'(?:^|::)([A-Z][A-Za-z0-9_]*|u8|u32|u64|usize)(?:::|<)',call)
   if mr:receiver=mr[1]
  if receiver:
   direct=[]
   for k,t in candidates:
    sig=k[k.find('(_1:'):] if '(_1:' in k else k[k.find('()'):];carriers=re.findall(r'(?:\(_1: | -> )(?:&(?:mut )?)?([A-Za-z_][A-Za-z0-9_:]*)',sig)
    if any(v.split('::')[-1]==receiver for v in carriers):direct.append((k,t))
   if direct:candidates=direct
  shorts=[(k,t) for k,t in candidates if k.split('(',1)[0].endswith('::'+stripped) and '::<impl' not in k.split('(',1)[0]]
  if len(shorts)==1:candidates=shorts
  types=set(re.findall(r'\b(?:[A-Z][A-Za-z0-9_]+|u8|u16|u32|u64|usize|i32|i64)\b',call));types-={'T','A','N','Self','Result','Option','Fn','FnMut','FnOnce','Iterator','DoubleEndedIterator','ExactSizeIterator'}
  if types:
   matched=[(k,t) for k,t in candidates if any(v in types for v in t)]
   if matched:candidates=matched
  trait=re.search(r'^<.+ as (?:[A-Za-z0-9_:]+::)?([A-Za-z0-9_]+)(?:<.*>)?>::',call)
  if trait and len(candidates)>1:
   ts=[(k,t) for k,t in candidates if re.search(r'\b'+re.escape(trait[1])+r'(?:<| for | )',k)]
   if ts:candidates=ts
  elif types:
   inh=[(k,t) for k,t in candidates if ' for ' not in k and 'impl at ' not in k and any(v in types for v in t)]
   if inh:candidates=inh
  if method=='len' and ('slice::' in call or '<impl [' in call):
   cs=[(k,t) for k,t in candidates if k.startswith('core::') and '(_1: &[' in k]
   if cs:candidates=cs
  if call.startswith('<&['):
   cs=[(k,t) for k,t in candidates if '(_1: &[' in k and ('; N]' in k)==(';' in call.split(' as ',1)[0])]
   if cs:candidates=cs
  # Prefer the explicit defining crate, or this caller's crate for unqualified symbols.
  owner=key.split('::',1)[0];explicit=call.split('::',1)[0]
  preferred=explicit if explicit in ['core','alloc','std','aspis_core','aspis_statement','aspis_r1_cost_probe','sha2','digest','block_buffer','zeroize'] else owner
  local=[(k,t) for k,t in candidates if k.startswith(preferred+'::')]
  if local:candidates=local
  # Prefer namespace components explicitly present in the printed callee.
  parts=re.findall(r'[A-Za-z_]\w*',stripped)[:-1];parts=[v for v in parts if v not in [preferred,'impl'] and len(v)>1]
  if len(candidates)>1 and parts:
   scores=[sum(bool(re.search(r'\b'+re.escape(v)+r'\b',k)) for v in parts) for k,t in candidates];hi=max(scores)
   if hi:candidates=[v for v,score in zip(candidates,scores) if score==hi]
  # Resolve a qualified crate when possible. Short std reexports can refer to core/alloc.
  for cr in ['aspis_core','aspis_statement','aspis_r1_cost_probe','zeroize','sha2','digest','block_buffer']:
   if call.startswith(cr+'::'):
    narrowed=[(k,t) for k,t in candidates if k.startswith(cr+'::')]
    if narrowed:candidates=narrowed
  if len(candidates)==1:resolved.add(candidates[0][0])
  elif 1<len(candidates)<=8:
   # Keep all alternatives as a conservative static envelope, never label them dynamically reached.
   unknown.append(dict(call=call,reason='ambiguous printed MIR symbol',candidates=[k for k,t in candidates]));resolved.update(k for k,t in candidates)
  else:unknown.append(dict(call=call,reason='no uniquely resolved body',candidate_count=len(candidates)))
 cache[c]=(sorted(resolved),unknown);return cache[c]

def root(crate,method,contains=(),exclude=()):return dict(crate=crate,method=method,contains=list(contains),exclude=list(exclude))
R={
'V164':root('aspis_statement','compress_tagged_tuple'),'V169':root('core','take',('(_1: &mut T)',)),
'V170':root('alloc','drop',('drop(_1: &mut Vec<T, A>)',)),
'V177':root('std','deref',('PathBuf',)), 'V178':root('std','join',('impl Path>',)),
'V179':root('std','as_ref',('for String','-> &Path')), 'V180':root('std','as_ref',('for PathBuf','-> &Path')),
'V181':root('alloc','with_capacity',('impl String',)), 'V182':root('alloc','push_str',('impl String',)),
'V183':root('alloc','try_reserve_exact',('try_reserve_exact(_1: &mut Vec<T, A>',)), 'V184':root('alloc','pop',('Vec<T, A>',)),
'V185':root('alloc','is_empty',('Vec<T, A>',)), 'V186':root('alloc','default',('default() -> Vec<T>',)),
'V187':root('alloc','try_from',('try_from(_1: Vec<T, A>) -> Result<[T; N]',)), 'V195':root('aspis_core','to_le_bytes',('WideExact',)),
'V197':root('aspis_core','from_le_bytes',('impl QM31',)), 'V198':root('aspis_core','write_le_bytes',('impl QM31',)),
'V199':root('aspis_core','clone',('domain::','&Point')), 'V201':root('aspis_core','eval_message'),
'V202':root('aspis_core','phi_inverse'), 'V206':root('aspis_core','leaf',('aspis_core::leaf(',)), 'V209':root('aspis_core','neg',('CodeField for WideExact',)),
'V210':root('aspis_core','neg',('CodeField for QM31',)), 'V211':root('aspis_core','try_inv',('CodeField for M31',)),
'V212':root('aspis_core','try_inv',('CodeField for QM31',)), 'V213':root('aspis_core','try_inv',('CodeField for WideExact',)),
'V214':root('aspis_core','from_m31',('CodeField for WideExact',)),
'V216':root('aspis_core','eq',('StateOnlyHidingContext',)), 'V217':root('aspis_core','state_only_selected_mask_value'),
'V218':root('aspis_core','statement_points'), 'V219':root('aspis_core','state_only_boundary_sum'),
'V220':root('aspis_core','evaluate_state_only_polynomial'),
'V221':root('zeroize','zeroize',('zeroize(_1: &mut [Z; N])',)), 'V222':root('zeroize','zeroize',('zeroize(_1: &mut Z)',)),
'V223':root('zeroize','deref',('Zeroizing',)), 'V224':root('zeroize','new',('Zeroizing',)),
'V226':root('zeroize','zeroize',('Zeroizing',)), 'V227':root('zeroize','as_ref',('Zeroizing',)),
'V229':root('aspis_statement','pool_v1_pair_forest_copy_active_rows_v1'),
'V230':root('aspis_statement','pool_v1_pair_forest_copy_active_row_masks_v1'),
'V231':root('sha2','finalize_variable_core',('for Sha256VarCore',)),
'V233':root('block_buffer','split_blocks',('for super::Eager',)),
'V234':root('digest','finalize',('finalize(_1: D) -> GenericArray',)),
'V235':root('digest','finalize_into',('CoreWrapper',)), 'V236':root('digest','update',('update(_1: &mut CoreWrapper<T>',)),
'V237':root('digest','default',('default() -> CoreWrapper<T>',)), 'V238':root('digest','finalize_fixed_core',('CtVariableCoreWrapper',)),
'V239':root('aspis_statement','multilinear_evaluate_qm31'), 'V240':root('aspis_statement','compress_tagged_tuple'),
'V242':root('aspis_statement','transition',('Public',)), 'V246':root('aspis_statement','eq',('PoolV1PairLatePublicStatementV1',)),
'V247':root('aspis_statement','state_only_copy_helper_sum'), 'V254':root('aspis_r1_cost_probe','binary_parent'),
'V256':root('aspis_r1_cost_probe','gamma_sample',('aspis_r1_cost_probe::sampler::',)), 'V257':root('aspis_r1_cost_probe','ordinary_sample',('aspis_r1_cost_probe::sampler::',)),
'V258':root('aspis_r1_cost_probe','materialize',('::weights::<',)),
'V259':root('aspis_r1_cost_probe','new',('::weights::<',)),
'V260':root('aspis_r1_cost_probe','raw',('::weights::<',)),
'V261':root('aspis_r1_cost_probe','powers',('prover_powers',)),
'V264':root('aspis_r1_cost_probe','all_slots_clear'), 'V265':root('aspis_r1_cost_probe','circle_sample',('sampler::',)),
}
constants={'V204','V205','V208','V215','V270'}
rows=json.loads((D/'selected-rows.json').read_text());out=[]
for r in rows:
 id=r['id']
 if id not in ['V169','V197','V201','V212','V213','V216','V217','V218','V220','V221','V222','V233','V236','V237','V246','V260','V265']:continue
 res=dict(id=id,name=r['name'],root_selector=R.get(id))
 if id in constants:res.update(status='STANDS',reason='constant or rejected diagnostic route; no native-link body credited',reached_functions=[],changed_functions=[],unresolved=[]);out.append(res);continue
 spec=R[id];roots={}
 for c in nodes:
  roots[c]=[k for k,t in indexes[c].get(spec['method'],[]) if k.startswith(spec['crate']+'::') and all(s in k for s in spec['contains']) and not any(s in k for s in spec['exclude'])]
 res['roots']=roots;reached={};unknown=[]
 for cohort in nodes:
  pending=roots[cohort][:];seen=set()
  while pending:
   k=pending.pop()
   if k in seen:continue
   seen.add(k);es,us=edges(cohort,k)
   unknown.extend(dict(cohort=cohort,function=k,**u) for u in us)
   pending.extend(x for x in es if x not in seen)
   if len(seen)>3000:unknown.append(dict(cohort=cohort,reason='static envelope over 3000; not a complete reached-body certificate'));break
  reached[cohort]=sorted(seen)
 allkeys=sorted(set(reached['old'])|set(reached['deployed']));changed=[]
 for k in allkeys:
  aa=nodes['old'].get(k);bb=nodes['deployed'].get(k)
  if aa!=bb:changed.append(dict(function=k,old_sha256=hashlib.sha256(aa.encode()).hexdigest() if aa else None,deployed_sha256=hashlib.sha256(bb.encode()).hexdigest() if bb else None,source='own cohort MIR' if k.startswith('aspis_') else 'sysroot/dependency MIR',reached_in=[c for c in reached if k in reached[c]]))
 certain={}
 for cohort in nodes:
  todo=roots[cohort][:] if len(roots[cohort])==1 else [];seen=set()
  while todo:
   k=todo.pop()
   if k in seen:continue
   seen.add(k);es,us=edges(cohort,k);ambiguous={v for u in us for v in u.get('candidates',[])};todo.extend(e for e in es if e not in ambiguous and e not in seen)
  certain[cohort]=sorted(seen)
 res['parametric_boundaries']=[dict(cohort=c,function=k,call=call) for c in nodes for k in reached[c] for call in re.findall(r'(?:= )?(<[A-Z] as [^\n]+?)\([^\n]*? -> \[return:',nodes[c][k])]
 res['certainly_reached_functions']=certain
 res['certainly_reached_changed_functions']=[x for x in changed if any(x['function'] in certain[c] for c in certain)]
 res['reached_functions']=reached;res['changed_functions']=changed;res['unresolved']=unknown
 res['status']='STANDS' if all(roots.values()) and not changed and not unknown else 'SUSPENDED'
 res['reason']='all resolved reached bodies identical' if res['status']=='STANDS' else 'body differs' if changed else 'complete body identity not established; unresolved MIR symbol/root'
 res['reachability_scope']='conservative static MIR envelope; ambiguous alternatives retained and explicitly listed; not certified dynamic/monomorphized reachability'
 out.append(res)
with lzma.open(O/'reached-audit.json.xz','wt') as f:json.dump(out,f)
(O/'root-audit.json').write_text(json.dumps([dict(id=x['id'],roots=x.get('roots'),status=x['status'],changed=len(x['changed_functions']),unresolved=len(x['unresolved'])) for x in out],indent=2))
print(json.dumps(json.loads((O/'root-audit.json').read_text()),indent=2))

(O/'typed-decisions.json').write_text(json.dumps(typed_decisions,indent=2)+'\n')
