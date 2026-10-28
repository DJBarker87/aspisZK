"""Lift hash/store callbacks and recursively splice explicitly selected helpers.
The erasure theorem uses the original frozen bodies and complete Result.
Opaque leaves stay in the emitted census, never silently become pure.
"""
from pathlib import Path
import sys,runpy,re,json,hashlib
args=sys.argv[1:];sys.argv=[sys.argv[0],'NONE'];g=runpy.run_path(str(Path(__file__).with_name('reify-recursive.py')));sys.argv=[sys.argv[0],*args]
R,D,E=g['R'],g['D'],g['E'];source=g['source'];s=g['s'];get=g['get'];parse=g['parse'];normalize=g['normalize'];spaces=g['spaces']
CONFIG=[
 ('aspis_prover.state_only_entropy.sync_directory','SyncDirectory'),
 ('aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path','ReservationPath'),
 ('aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reserve_fallible','ReserveFallible'),
 ('aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve','DurableReserve'),
 ('aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve','PreReservedReserve'),
 ('aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1','ReserveBuild'),
 ('aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref','MaskMaterial'),
 ('aspis_prover.state_only_hiding.apply_pool_v1_pair_forest_mask_material_v1','ApplyMaterial'),
 ('aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets.derive_pool_v1_pair_forest_zero_factor_d','ZeroFactor'),
 ('prover.fixed_k_column','FixedColumn'),
 ('prover.audit_masks','AuditMasks'),
 ('prover.derive_private_salt_step','PrivateSaltStep'),
 ('prover.derive_private_salts_loop.body','PrivateSaltsBody'),
 ('prover.audit_masks_loop0.body','AuditMasksBody0'),
 ('prover.audit_masks_loop1.body','AuditMasksBody1'),
 ('prover.inactive_sum_k_loop.body','InactiveSumBody'),
 ('prover.opening_inactive_loop.body','OpeningInactiveBody'),
 ('prover.opening_batch_loop.body','OpeningBatchBody'),
 ('prover.derive_private_salts','PrivateSalts'),
 ('prover.prepare_opening','PrepareOpening'),
 ('prover.finish_opening','FinishOpening'),
 ('prover.publish_compact','PublishCompact'),
 ('host_semantic.build_with_material','HostBuild'),
 ('prover.prove_from_semantics','FromSemantics'),
 ('prover.prove_masked_with_attempt','MaskedWithAttempt'),
 ('prover.prove_masked_attempt','Entry'),
]
M={name:short for name,short in CONFIG if short!='HostBuild'};meta={name:get(name) for name,_ in CONFIG}
DICT={
 'aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore':'DurableReserve',
 'aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore':'PreReservedReserve',
}
constructors={'std.fs.File.open':'fileOpen','std.fs.File.sync_all':'fileSync','std.fs.OpenOptions.open':'optionsOpen','std.io.error.Error.kind':'errorKind','std.fs.File.Insts.StdIoWrite.write_all':'writeAll'}
current=None;callbacks=[];imports=set();calls=[]
def info(header):
 result=[]
 if re.search(r'\(hash : Slice \(Slice Std.U8\) → Result \(Array Std.U8 32#usize\)\)',header):result.append(('hash','Hash'))
 for name in re.findall(r'\((\w+)\s*:\s*aspis_prover\.state_only_hiding\.StateOnlyMaskNonceStore T0\)',header):result.append((name,'Store'))
 return result

def emit(node,n=2,inBind=False):
 pad=' '*n;k=node.kind
 if k=='let':return spaces('\n'.join(x.strip() for x in node.text.splitlines()),n)+'\n'+emit(node.next,n)
 if k=='bind':
  exp=emit(node.expr,n+2,True);structured=node.expr.kind not in ['call','pure']
  if structured:
   return pad+'PV_W_StructuredBinds.join (do\n'+exp+') (fun '+node.var+' => do\n'+emit(node.next,n+2)+')'
  return pad+'let '+node.var+' ← '+exp.lstrip()+'\n'+emit(node.next,n)
 if k=='if':return pad+'if '+node.cond+' then\n'+emit(node.yes,n+2)+'\n'+pad+'else\n'+emit(node.no,n+2)
 if k=='match':return pad+'match '+node.discr+' with\n'+'\n'.join(pad+'| '+p+' =>\n'+emit(c,n+2) for p,c in node.branches)
 if k=='pure':return pad+'pure '+node.expr.replace('\n','\n'+pad+'  ')
 expr=node.expr;label=expr.split()[0];inline=M.get(label)
 if label==current:inline=None
 calls.append(dict(label=label,expression=expr,classification='recursive' if inline else 'callback' if label=='hash' or '.«reserve»' in label else 'typed primitive' if label in constructors or label=='alloc.vec.Vec.try_reserve_exact' else 'opaque obligation'))
 if inline:
  imports.add(inline);expr='PV_W_R_'+inline+'.program'+expr[len(label):]
  for d,target in DICT.items():
   if d in expr:imports.add(target);expr=expr.replace(d,'PV_W_R_'+target+'.store')
  return spaces(expr,n) if inBind or '\n' not in expr else pad+'('+expr.replace('\n','\n'+pad+'  ')+')'
 if label=='hash':return spaces(expr,n)
 if label.endswith('.«reserve»') and any(label.startswith(x+'.') for x,t in callbacks if t=='Store'):
  return spaces(expr.replace('.«reserve»','.reserve'),n)
 if label=='alloc.vec.Vec.try_reserve_exact':return pad+'perform (.reserve '+expr[len(label):].strip()+')'
 if label in constructors:
  rest=expr[len(label):].strip()
  if label in ['std.fs.File.open','std.fs.OpenOptions.open']:
   if rest[0]=='(':
    depth=0
    for cut,ch in enumerate(rest):
     if ch=='(':depth+=1
     elif ch==')':
      depth-=1
      if depth==0:cut+=1;break
   else:cut=len(rest.split()[0])
   conv=rest[:cut];rest='(fun dictionary => letI : ExternalFuns := dictionary; '+conv+') '+rest[cut:].strip()
  return pad+'perform (.base (.'+constructors[label]+' '+rest+'))'
 binds=''.join(pad+'  let '+name+' := source'+kind+' ops '+name+'\n' for name,kind in callbacks)
 return pad+'invoke '+json.dumps(label,ensure_ascii=False)+' (fun ops =>\n'+pad+'  letI : ExternalFuns := ops\n'+binds+spaces(expr,n+2)+')'

def proof(node,n=2):
 pad=' '*n;k=node.kind
 if k=='let':return pad+'try dsimp only\n'+proof(node.next,n)
 if k=='bind':
  var=node.var;intro=('rintro ⟨'+var[1:-1]+'⟩') if var.startswith('(') else 'intro '+var
  return (pad+'try dsimp only\n' if node.expr.kind in ['call','pure'] else '')+pad+('rw [erase_bind]' if node.expr.kind in ['call','pure'] else 'rw [PV_W_StructuredBinds.erase_join]')+'\n'+pad+'apply PV_W_RecursiveLaws.bind_congr\n'+pad+'·\n'+proof(node.expr,n+2)+'\n'+pad+'· '+intro+'\n'+proof(node.next,n+2)
 if k=='if':return pad+'try dsimp only\n'+pad+'apply PV_W_Callbacks.erase_if_congr\n'+pad+'·\n'+proof(node.yes,n+2)+'\n'+pad+'·\n'+proof(node.no,n+2)
 if k=='match':
  out=pad+'try dsimp only\n'+pad+'cases '+node.discr+' with\n'
  for ix,(p,c) in enumerate(node.branches):
   ps=p.split();ctor=ps[0].split('.')[-1];aa=[('unused'+str(ix)+'_'+str(i)) if a=='_' else a for i,a in enumerate(ps[1:])]
   out+=pad+'| '+ctor+(' '+' '.join(aa) if aa else '')+' =>\n'+proof(c,n+2)+'\n'
  return out.rstrip()
 if k=='pure':return pad+'rfl'
 label=node.expr.split()[0];inline=M.get(label) if label!=current else None
 if inline:
  used=[target for d,target in DICT.items() if d in node.expr]
  laws=['PV_W_R_'+inline+'.erase_program']+['PV_W_R_'+x+'.store_source' for x in used]
  return pad+'rw ['+','.join(laws)+']'
 if label=='hash' or label.endswith('.«reserve»'):return pad+'rfl'
 if label in constructors or label=='alloc.vec.Vec.try_reserve_exact':return pad+'exact erase_perform ops _'
 return pad+'exact erase_invoke ops _ _'

selected=args[0]
for name,short in CONFIG:
 if selected not in [short,'ALL']:continue
 current=name;header,result,body,aa,explicit=meta[name];callbacks=info(header);imports=set();calls=[]
 h=header
 for cb,kind in callbacks:
  if kind=='Hash':h=re.sub(r'\(hash : Slice \(Slice Std.U8\) → Result \(Array Std.U8 32#usize\)\)', '(hash : Hash)',h)
  else:h=re.sub(r'\('+cb+r'\s*:\s*aspis_prover\.state_only_hiding\.StateOnlyMaskNonceStore T0\)', '('+cb+' : Store T0)',h)
 node=parse(normalize(body));translated=emit(node);pr=proof(node)
 actualargs=[]
 for a in aa:
  kind=next((t for n,t in callbacks if n==a),None)
  actualargs.append('(source'+kind+' ops '+a+')' if kind else a)
 pre='import R1Z.PV_W_StructuredBinds\nimport R1Z.PV_W_RecursiveLaws\n'+''.join('import R1Z.PV_W_R_'+x+'\n' for x in sorted(imports))
 pre+=('open Aeneas.Std.ControlFlow\n' if re.search(r'\b(?:cont|done)\b',body) else '')
 out=pre+'set_option autoImplicit false\nnoncomputable section\nnamespace R1Z.PV_W_R_'+short+'\nopen Aeneas Aeneas.Std ProverRwFull PV_W_ReachedEffects PV_W_Callbacks\nvariable [ExternalTypes]\n\n'
 out+='def program\n  '+h+' :\n  P '+result+' := do\n'+translated+'\n\n'
 out+='theorem erase_program (ops : ExternalFuns)\n  '+h+' :\n  erase ops (program '+' '.join(explicit)+') =\n    @'+name+(' ' if short=='PreReservedReserve' else ' _ ops ')+' '.join(actualargs)+' := by\n  unfold program '+name+'\n'+pr+'\n\n#print axioms erase_program\n'
 if short in ['PreReservedReserve','DurableReserve']:
  typ='aspis_prover.state_only_entropy.'+('PreReservedNonce' if short=='PreReservedReserve' else 'DurableStateOnlyMaskNonceStore')
  inst=next(d for d,x in DICT.items() if x==short)
  out+='\ndef store : Store '+typ+' := ⟨program⟩\n\ntheorem store_source (ops : ExternalFuns) :\n    sourceStore ops store = @'+inst+('' if short=='PreReservedReserve' else ' _ ops')+' := by\n  apply congrArg aspis_prover.state_only_hiding.StateOnlyMaskNonceStore.mk\n  funext self a b\n  exact erase_program ops self a b\n\n#print axioms store_source\n'
 out+='end R1Z.PV_W_R_'+short+'\n'
 target=D/('PV_W_R_'+short+'.lean')
 if '--check' in args:assert target.read_text()==out
 else:target.write_text(out)
 (E/('d372-lift-'+short+'.json')).write_text(json.dumps(dict(source=source,body_sha256=hashlib.sha256(body.encode()).hexdigest(),name=name,module='R1Z.PV_W_R_'+short,callbacks=callbacks,recursive_imports=sorted(imports),calls=calls,scope='complete-Result source translation; remaining opaque leaves and native/deployment adequacy unproved'),indent=2)+'\n')
 print(short,len(calls),'calls;',len(imports),'recursive helpers;',callbacks)
