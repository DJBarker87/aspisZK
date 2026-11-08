# Bootstrap/review aid only: final accepted Lean sources are authoritative.
# This emits intermediate source, not a release/regeneration command.
"""Use NativeDelivery16.full, rather than re-derive interpreter administration."""
from pathlib import Path
P=Path(__file__).resolve().parents[3]/'lean'
for file,namespace,cfg,wait,token,a,dest,args,node,extras,answer in [
('TlsWorld18_1','TlsDelivery15','PV_LIB_SPEC_TlsAt54.config','PV_LIB_SPEC_TlsAt55.wait','PV_LIB_SPEC_TlsAt54.token',6,7,'[PV_LIB_SPEC_TlsAt54.initValue]',14,'PV_LIB_SPEC_TlsAt54.config','PV_LIB_SPEC_World18_TlsBound15.answer e stack resources'),
('TlsWorld18_2','Tls277Delivery15','PV_LIB_SPEC_Tls59Data15.config','PV_LIB_SPEC_Tls59Data15.wait','PV_LIB_SPEC_Tls59Data15.token',7,6,'[PV_LIB_SPEC_TlsNative15.reference]',17,'PV_LIB_SPEC_Tls59Data15.config,PV_THR2_RunTlsNext.pending','PV_LIB_SPEC_Tls277Bound15.answer (PV_LIB_SPEC_TlsNative15.cut stack) resources PV_LIB_SPEC_Tls59Data15.config e.world 7 PV_LIB_SPEC_Entry13.slot.source PV_LIB_SPEC_Tls59Data15.wait PV_LIB_SPEC_Tls59Data15.waiting rfl'),
]:
 p=P/('PV_LIB_SPEC_'+file+'.lean');s=p.read_text();start=s.index('theorem transition',s.index('namespace PV_LIB_SPEC_World18_'+namespace));begin=s.index(':= by',start);end=s.index('\n#print axioms transition',begin)
 head=s[start:begin];c=cfg
 body=f''':= by
  have lookup : PV_LIB_SPEC_Full.programs {token} = none := rfl
  have table : PV_LIB_StoreActionTable.v2 {token} = none := rfl
  change PV_LIB_SPEC_ReachedNative14.transition (PV_LIB_SPEC_TlsNative15.cut stack)
    (PV_LIB_SPEC_TlsBound15.parameters resources) {c}
    ⟨⟨.running {c},e.world,[]⟩,[]⟩ = _
  have quiet : PV_LIB_SPEC_SourceTransport15.Quiet ⟨⟨.running {c},e.world,[]⟩,[]⟩ := by
    simp [lookup,table,PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node{node},
      PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_StoreActionTable.Neutral,
      PV_LIB_StoreActionTable.select,{extras},{wait},
      PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,
      PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformNeutral.configuration,
      PV_THR2_OwnUniformNeutral.instruction]
  rw [PV_LIB_SPEC_NativeDelivery16.full (PV_LIB_SPEC_TlsNative15.cut stack)
    (PV_LIB_SPEC_TlsBound15.parameters resources) {c} e.world [] []
    {wait} {token} {a} {dest} {args}
    quiet (by rfl) rfl rfl (by rfl) rfl lookup]
  have reply := {answer}
  simp only [PV_LIB_SPEC_ReachedNative14.handler,reply,Option.getD_some]
  rfl
'''
 # expose wait request to match the native answer theorem
 body=body.replace('simp only [PV_LIB_SPEC_ReachedNative14.handler,reply,Option.getD_some]',f'simp only [PV_LIB_SPEC_ReachedNative14.handler,\n    show {wait}.request = '+('PV_LIB_SPEC_TlsNative15.request' if a==6 else 'PV_LIB_SPEC_Tls59Data15.request')+' from rfl,reply,Option.getD_some]')
 s=s[:start]+head+body+s[end:];p.write_text(s)
