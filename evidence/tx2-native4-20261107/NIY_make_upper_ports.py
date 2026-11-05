from NIY_port_tools import E,statement,head,context,params
import json
rows=[('NIY_AfterAlpha1','suffix','NIY_AfterRho','suffix','NIY_QueryPort','Rho','readK','unK','k_reverse'),('NIY_AfterAlpha0','suffix','NIY_AfterAlpha1','suffix','NIY_RhoReadPort','Alpha1','readE','unE','e_reverse'),('NIY_AfterKappa','suffix','NIY_AfterAlpha0','suffix','NIY_Alpha1ReadPort','Alpha0','readE','unE','e_reverse'),('NIY_FirstECut','afterGamma','NIY_AfterKappa','suffix','NIY_Alpha0ReadPort','Kappa','readE','unE','e_reverse'),('NIY_FirstRawCut','freshAfterRaw','NIY_FirstECut','afterGamma','NIY_KappaReadPort','Gamma','readE','unE','e_reverse')]
mods=[]
for prev,fn,split,sfn,nextport,label,op,un,reverse in rows:
 ns='NIY_'+label+'ReadPort';p,ctx,fa,ca,st=statement(prev,fn);nctx=context(params(split,sfn));existing={n for n,t in ctx};freshnames=[n for n,t in nctx if n not in existing];assert len(freshnames)==2,(prev,freshnames)
 value,reader=freshnames;call=' '.join('('+un+' value)' if n==value else '(unReader out)' if n==reader else n for n,t in nctx)
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
(E/'NIY_UPPER_PORT_MODULES.json').write_text(json.dumps(mods,indent=2)+'\n')
print('Authored upper five typed transports with the SAME state, roots, returned field value and reader carrier.')
