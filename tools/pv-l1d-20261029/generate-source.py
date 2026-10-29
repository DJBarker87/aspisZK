"""Generate source-parametric phase interpreters, never a native fidelity claim.
The selected emitted body is retained verbatim, with a Logged coercion for Result
and an entry marker. A prior interpreter is composed only in direct do actions;
loop functional arguments remain explicit uninstrumented frontier edges.
"""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l1d-20261029';D=R/'lean'
sources=json.loads((E/'focused-project-sources.json').read_text());s=sources['R1Z.ProverRwFullFuns'];all_defs={}
starts=list(re.finditer(r'^def (\S+)',s,re.M))
for i,m in enumerate(starts):
 raw=s[m.start():starts[i+1].start() if i+1<len(starts) else len(s)]
 end=raw.find('\n/--');raw=raw[:end] if end>=0 else raw
 raw=re.sub(r'\n(?:@\[.*?\]|partial_fixpoint)\s*$','',raw).rstrip()
 if '\n  := do\n' in raw:all_defs[m[1]]=raw
# The public control/error/phase frontier, before arithmetic-only leaves.
selected=[n for n in all_defs if n.startswith(('prover.','host_semantic.','host_transcript.','host_sumcheck.')) and not any(x in n for x in ['closure','Insts.','_loop'])]
# Loop bodies at the observable query/canonicality/audit frontier are necessary
# for a later bounded logged-loop composition; avoid unrelated arithmetic loops.
selected += [n for n in all_defs if n.startswith(('host_transcript.','host_semantic.check_','prover.audit_masks_','prover.derive_private_salts_')) and n.endswith('.body') and n not in selected]
selected=[n for n in selected if not (n.startswith('host_sumcheck.') and not n.startswith('host_sumcheck.prove_sumcheck')) and not any(n==x for x in ['prover.fold','prover.fold_cell','prover.round','prover.encoded_slice','host_semantic.copy_cell','host_semantic.copy_tuple_limb','host_semantic.copy_tuple_values','host_semantic.copy_endpoint_values','host_semantic.lean_copy_row_values','host_semantic.column_coefficients','host_semantic.boolean_point','host_semantic.lift'])]
# Keep the generator's dependency/source order. Recursive and loop edges stay native.
selected=sorted(set(selected),key=lambda n:list(all_defs).index(n))
rows=[];known={}
accepted={}
def binders(h):
 out=[];depth=0;begin=None
 for i,c in enumerate(h):
  if c in '({[':
   if depth==0:begin=i
   depth+=1
  elif c in ')}]':
   depth-=1
   if depth==0 and begin is not None:
    group=h[begin+1:i]
    if ':' in group:
     names=group.split(':',1)[0].strip().split()
     out.extend((n,h[begin]) for n in names)
 return out
for k,n in enumerate(selected):
 raw=all_defs[n];h,b=raw.split('\n  := do\n',1);sig=h[len('def '+n):];pos=sig.rfind('\n  Result')
 if pos<0:continue
 params=sig[:pos];ret=sig[pos:];args=binders(params)
 if not args:continue
 mod='PV_L1D_Source_'+str(k).zfill(3);site='opening'
 if n.startswith('host_semantic.') :site='semanticCanonical'
 if n.startswith('host_sumcheck.') :site='boundary 0'
 if n.startswith('host_transcript.') :site='queryScan' if 'quer' in n else 'opening'
 if 'audit' in n or 'inactive_sum' in n:site='balanceAudit'
 if 'salt' in n:site='saltDerivation'
 if 'publish' in n or 'append_' in n or 'publication' in n:site='publication'
 if 'public_check' in n:site='checker'
 if 'prove_masked' in n:site='callback'
 # Do not rewrite higher-order loop body arguments or original recursion. Each
 # retained edge is listed so entry markers cannot be misreported as full traces.
 deps=[];body=b
 for dep,dm in sorted(known.items(),key=lambda x:-len(x[0])):
  if dep==n or dep.endswith('.body') or dep.endswith('_loop'):continue
  if re.search(r'(?m)^(\s*)'+re.escape(dep)+r'(?=\s|$)',body):
   body=re.sub(r'(?m)^(\s*)'+re.escape(dep)+r'(?=\s|$)',lambda m:m[1]+dm+'.produce',body);deps.append(dm)
 # Explicit lifts let dependent-array sizes be inferred from the source action
 # before the Logged bind elaborates its continuation.
 lines=body.splitlines()
 for at in reversed(range(len(lines))):
  line=lines[at]
  if '←' not in line or not re.match(r'\s*let\b',line):continue
  indent=len(line)-len(line.lstrip());end=at+1
  while end<len(lines) and (not lines[end].strip() or len(lines[end])-len(lines[end].lstrip())>indent):end+=1
  prefix,first=line.split('←',1);expr='\n'.join([first.strip()]+lines[at+1:end]).strip()
  if re.match(r'PV_L1D_(?:Source_\d+|QueryProducer)\.produce\b',expr):continue
  lines[at:end]=[(prefix+'← PV_L1D_Logged.lift ('+expr+')')]
 body='\n'.join(lines)
 body=re.sub(r'(?<![A-Za-z0-9_.])ok(?=\s|\()', 'Pure.pure', body)
 body=re.sub(r'(?<![A-Za-z0-9_.])(sampler|host_sampler)\.',r'ProverRwFull.\1.',body)
 applications=' '.join(('('+x+' := '+x+')') if kind=='{' else x for x,kind in args)
 result_sig=ret.replace('\n  Result','\n  Logged',1)
 # Parenthesize the parameterized Call.boundary constructor.
 marker='('+('.'+site)+')' if ' ' in site else '.'+site
 code='import PV_L1D_ResultCoercion\nimport PV_L1D_Projection\nimport PV_L1D_EraseIf\nimport R1Z.ProverRwFullFuns\n'+''.join('import '+d+'\n' for d in sorted(set(deps)))
 code+='set_option autoImplicit false\nnoncomputable section\nnamespace '+mod+'\nopen Aeneas Aeneas.Std Result ControlFlow ProverRwFull\nopen PV_L1D_Logged\nvariable [ExternalTypes] [ExternalFuns]\n'
 code+='\n/-- Source-parametric phase entry and complete Result. Remaining loop and\nopaque/native event edges are recorded in source-frontier.json. -/\n'
 code+='def produce'+params+result_sig+'\n  := do\n  let _ ← observe '+marker+' 0 (ok ())\n'+body+'\n\n'
 code+='theorem complete_result'+params.rstrip().removesuffix(':').rstrip()+' :\n  erase (produce '+applications+') = '+n+' '+applications+' := by\n'
 code+='  unfold produce\n  conv_rhs => unfold '+n+'\n'
 lemmas=['PV_L1D_EraseIf.erase_if','PV_L1D_Projection.prod_case','Aeneas.Std.bind_tc_ok','erase_bind','erase_observe','erase_lift','erase_coe','erase_pure']+[d+'.complete_result' for d in sorted(set(deps))]
 simp='simp only ['+','.join(lemmas)+']'
 code+='  '+simp+'\n  repeat\' first\n    | with_reducible rfl\n    | split <;> '+simp+'\n    | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr\n      intro value called\n'
 code+="  all_goals\n    cases value\n    repeat' first\n      | with_reducible rfl\n      | apply (Aeneas.Std.bind_eq_iff _ _ _).mpr\n        intro value called\n      | split <;> "+simp+"\n    all_goals rfl\n"
 if n=='host_semantic.zc_rows':
  proof_start=code.index(' := by\n',code.index('theorem complete_result'))
  code=code[:proof_start]+" := by\n  unfold produce\n  conv_rhs => unfold host_semantic.zc_rows\n  simp only [erase_bind,erase_observe,erase_lift,Aeneas.Std.bind_tc_ok]\n  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr\n  intro zero hz\n  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr\n  rintro ⟨tr1,bs1,zc1,pending⟩ hr\n  cases pending <;> rfl\n"
 code+='#print axioms complete_result\nend '+mod+'\n'
 path=D/(mod+'.lean')
 if mod in accepted:
  assert hashlib.sha256(path.read_bytes()).hexdigest()==accepted[mod]['source_sha256'],('accepted source changed',mod)
 else:path.write_text(code)
 rows.append(dict(module=mod,source_function=n,path=str(path.relative_to(R)),source_body_sha256=hashlib.sha256(raw.encode()).hexdigest(),source_module_sha256=hashlib.sha256(s.encode()).hexdigest(),dependencies=sorted(set(deps)),native_edges=sorted(set(re.findall(r'\b(?:prover|host_semantic|host_transcript|host_sumcheck)\.[\w.]+',body))),discarded_restoration_candidates=re.findall(r'^.*(?:let\s+\([^\n]*,\s*_\)|next_back.*_).*$' ,raw,re.M),evidence_class='emission/model complete-Result law only; native fidelity and loop payload frontier open'))
 known[n]='PV_L1D_QueryProducer' if n=='host_transcript.Transcript.queries' else mod
(E/'source-frontier.json').write_text(json.dumps(rows,indent=2)+'\n');print('Generated',len(rows),'source phase modules')
