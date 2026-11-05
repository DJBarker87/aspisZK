from NIY_port_tools import E,statement,head,context,params
import json
# Bottom-up real dependencies, from final allocation towards the semantic section.
rows=[('NIY_AfterRhs','NIY_AfterPower','NIY_AllocationPort','Power','readK','unK','k_reverse'),('NIY_AfterClaim','NIY_AfterRhs','NIY_PowerReadPort','Rhs','readE','unE','e_reverse'),('NIY_AfterZ1y','NIY_AfterClaim','NIY_RhsReadPort','Claim','readE','unE','e_reverse'),('NIY_AfterZ1x','NIY_AfterZ1y','NIY_ClaimReadPort','Z1y','readK','unK','k_reverse'),('NIY_AfterZ0y','NIY_AfterZ1x','NIY_Z1yReadPort','Z1x','readK','unK','k_reverse'),('NIY_AfterZ0x','NIY_AfterZ0y','NIY_Z1xReadPort','Z0y','readK','unK','k_reverse'),('NIY_SemanticCut','NIY_AfterZ0x','NIY_Z0yReadPort','Z0x','readK','unK','k_reverse')]
mods=[]
for prev,split,nextport,label,op,un,reverse in rows:
 ns='NIY_'+label+'ReadPort';p,ctx,fa,ca,st=statement(prev,'suffix');nctx=context(params(split,'suffix'));existing={n for n,t in ctx};freshnames=[n for n,t in nctx if n not in existing];assert len(freshnames)==2,(prev,freshnames)
 value,reader=freshnames
 call=' '.join('('+un+' value)' if n==value else '(unReader out)' if n==reader else n for n,t in nctx)
 out=head(ns,[nextport,split,'NIY_C_'+split.removeprefix('NIY_'),'NIL_PortBind'])+'\ntheorem source '+p+' :\n'+st+f''' := by
 with_unfolding_all rw [{split}.source,NIY_C_{split.removeprefix('NIY_')}.source]
 unfold NIL_StatePort.reply NIL_FreshOps.{op}
 apply NIL_PortBind.read {un} unReader NIL_StatePort.pair
 intro value out
 have h := {nextport}.source reserved d bytes v end1 i4 {call}
 simpa only [NIL_StatePort.reply,{reverse},reader_reverse] using h
#print axioms source
end {ns}
'''
 (E/(ns+'.lean')).write_text(out);mods.append(ns)
(E/'NIY_TYPED_PORT_MODULES.json').write_text(json.dumps(mods,indent=2)+'\n')
print('Authored seven bottom-up read transports, each using NIL_PortBind.read on the same reader/value carrier.')
