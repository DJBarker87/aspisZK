from pathlib import Path
segs=[('PV_LIB_A_F6SourceSequences14','E','seqE','offE',False),
 ('PV_LIB_A_PrefixStructuredCalls14','125','','',False),
 ('PV_LIB_A_F125Prologue13','','seq','off',False),
 ('PV_LIB_A_PrefixStructuredCalls14','219','','',False),
 ('PV_LIB_A_F219Prologue13','','seq','off',False),
 ('PV_LIB_A_PrefixNativeCalls14','134','','',True),
 ('PV_LIB_A_F219CallbackHistory14','1','seq','off',False),
 ('PV_LIB_A_V2Callback14','','callback','',False),
 ('PV_LIB_A_F316Prefix13','','seq','off',False),
 ('PV_LIB_A_PrefixNativeCalls14','410','','',True),
 ('PV_LIB_A_F316ToInvoke13','','seq','off',False),
 ('PV_LIB_A_PrefixStructuredCalls14','220','','',False),
 ('PV_LIB_A_F220Prefix14','','seq','off',False),
 ('PV_LIB_A_PrefixStructuredCalls14','208','','',False),
 ('PV_LIB_A_F208Prefix14','','seq','off',False),
 ('PV_LIB_A_PrefixStructuredCalls14','15','','',False)]
imports=list(dict.fromkeys(m for m,_,_,_,_ in segs))+['PV_LIB_A_V2ActualBindings14','PV_LIB_A_V2Composition14','PV_LIB_A_Full124TableGap14']
s=''.join('import '+m+'\n' for m in imports)+'''set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_V2Post124To15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary PV_LIB_StoreActionTable
open PV_LIB_A_V2Composition14 PV_LIB_A_StructuredFrontier13

/-- Exact post124 source table fragment, COMPATIBLE with the Full BODY table.
In particular this asks for NO native124 reply. -/
structure Lookups (P : Data → Option PV_STX2_SliceSyntax.Program) : Prop where
  native134 : P (fn PV_LIB_A_PrefixNativeCalls14.src134) = none
  native410 : P (fn PV_LIB_A_PrefixNativeCalls14.src410) = none
'''
for id in ['125','219','220','208','15']:s+=f'  body{id} : P (fn PV_LIB_A_PrefixStructuredCalls14.src{id}) = some PV_THR2_F{id}.live\n'
s+='\ndef segments (C : Carrier OWNER Data) (H : Handler) : List Segment :=\n  [\n'
for i,(m,n,seq,off,h) in enumerate(segs):
 if seq=='callback':cost=m+'.steps';finish=m+'.after'
 elif m.endswith('CallbackHistory14'):cost=m+'.cost1 C';finish=m+'.finish1 C'
 else:cost=m+'.steps'+n+' C';finish=m+'.after'+n+' C'+(' H' if h else '')
 s+='    ⟨'+cost+','+finish+'⟩'+(',' if i<len(segs)-1 else '')+'\n'
s+='''  ]
def route (C : Carrier OWNER Data) (H : Handler) := chain (segments C H)

/-- ORIGINAL v2 post124 caller continuation through the actual callback chain
into15, or the first earlier source/native stop. All native FULL contracts and
source helpers are applied BY NAME. CLOSED124's actual Post store must first
be transported into this continuation; no opaque124 surrogate is used here. -/
theorem certified (base : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookups : Lookups P)
    (resources : Resources) (encode : Encode) (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) :
    let C := PV_THR2_EntryDynamic.carrier base b
    Certified C K P resources encode H values (route C H) := by
  intro C
  apply chained
  intro x hx
  simp [segments] at hx
  rcases hx with '''+' | '.join('h'+str(i) for i in range(len(segs)))+'\n'
for m,n,seq,off,h in segs:
 s+='  · subst x\n'
 if seq=='callback':s+=f'    exact {m}.run base b K P resources encode H values\n'
 elif seq:
  s+=f'    exact PV_LIB_A_V2Frontiers14.sequence C K P resources encode H values {m}.{seq} _ {m}.{off}\n'
 else:
  kind='native' if h else 'body'
  s+=f'    exact PV_LIB_A_V2ActualBindings14.run{n} C K P lookups.{kind}{n} resources encode H values\n'
s+='''
/-- Applied to a whole post124 source configuration, retaining exact worlds,
events, stores and callers. This is not original Entry14 reachability, complete
LoopInvariant initialization/preservation, or the14756 OwnInit witness. -/
theorem history (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (lookups : Lookups P)
    (resources : Resources) (encode : Encode) (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (q : State) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    PV_LIB_StoreActionTable.advance B K P resources encode H values ((route B H).steps q) q = (route B H).after q :=
  certified (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier (PV_THR2_RangeLiterals.carrier C)))
    b K P lookups resources encode H values q

#print axioms segments
#print axioms route
#print axioms certified
#print axioms history
end PV_LIB_A_V2Post124To15
'''
Path('lean/PV_LIB_A_V2Post124To15.lean').write_text(s)
