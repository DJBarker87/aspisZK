from pathlib import Path
# (module, suffix, handler-dependent, proof-program-argument)
segs=[]
def add(m,n='',h=False,p='table'):segs.append((m,n,h,p))
for letter,native in [('A','121'),('B','122'),('C','123'),('D','124')]:
 add('PV_LIB_A_F6SourceSequences14',letter)
 add('PV_LIB_A_PrefixNativeCalls14',native,True,'P')
add('PV_LIB_A_F6SourceSequences14','E')
add('PV_LIB_A_PrefixStructuredCalls14','125',p='P')
add('PV_LIB_A_F125Prologue13')
add('PV_LIB_A_PrefixStructuredCalls14','219',p='P')
add('PV_LIB_A_F219Prologue13')
add('PV_LIB_A_PrefixNativeCalls14','134',True,'P')
add('PV_LIB_A_F219CallbackHistory14','1',p='special')
add('PV_LIB_A_F219Enter316Any14',p='callback')
add('PV_LIB_A_F316Prefix13')
add('PV_LIB_A_PrefixNativeCalls14','410',True,'P')
add('PV_LIB_A_F316ToInvoke13')
add('PV_LIB_A_PrefixStructuredCalls14','220',p='P')
add('PV_LIB_A_F220Prefix14')
add('PV_LIB_A_PrefixStructuredCalls14','208',p='P')
add('PV_LIB_A_F208Prefix14')
add('PV_LIB_A_PrefixStructuredCalls14','15',p='P')
imports=list(dict.fromkeys(m for m,_,_,_ in segs))+['PV_LIB_A_PrefixComposition14','PV_LIB_A_F6Counter11']
s=''.join(f'import {m}\n' for m in imports)+'''set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6To15Fixed14
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_StoreActionTable PV_THR2_SourceStoreLibrary PV_LIB_A_PrefixMachine11
open PV_LIB_A_PrefixComposition14
abbrev programs := PV_LIB_A_SpawnEnter12.enter270Programs

def segments (C : Carrier OWNER Data) (H : Handler) : List Segment :=
  [\n'''
for i,(m,n,h,p) in enumerate(segs):
 if p=='special':cost=f'{m}.cost1 C';finish=f'{m}.finish1 C'
 elif p=='callback':cost=f'{m}.steps';finish=f'{m}.after'
 else:cost=f'{m}.steps{n} C';finish=f'{m}.after{n} C'+(' H' if h else '')
 s+=f'    lift ({cost}) ({finish})'+(',' if i<len(segs)-1 else '')+'\n'
s+='''  ]
def prefix (C : Carrier OWNER Data) (H : Handler) := chain (segments C H)

/-- SAME fixed resolver from f6 entry through actual125/219/318/316/220/208
and15 BODY entry. Every native answer and every source gap stays at its actual
frontier; callback tokens/address/selection come from emitted stores. This does
not assert full LoopInvariant, native adequacy, full f6 Post or original entry. -/
theorem certified (base : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) :
    let C := PV_THR2_EntryDynamic.carrier base b
    Certified C K (programs P) resources encode H values (prefix C H) := by
  intro C
  apply chained
  intro x hx
  simp only [segments,List.mem_cons,List.mem_singleton] at hx
  rcases hx with '''+' | '.join(['h'+str(i) for i in range(len(segs))])+ '\n'
for i,(m,n,h,p) in enumerate(segs):
 s+='  · subst x\n    apply lifted\n'
 if p=='special':
  s+='    exact PV_LIB_A_SequenceFrontier13.run C K (programs P) resources encode H values\n      PV_LIB_A_F219CallbackHistory14.seq _ PV_LIB_A_F219CallbackHistory14.off\n'
 elif p=='callback':s+=f'    exact {m}.run base b K (programs P) resources encode H values\n'
 else:s+=f'    exact {m}.run{n} C K '+('P' if p=='P' else '(programs P)')+' resources encode H values\n'
s+='''
/-- Whole BODY-entry equation, without a saved callback/decoder/native-success
premise. The resulting expression retains exact failure/pending source frontiers. -/
theorem history (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    let B := PV_LIB_A_F6Counter11.carrier C b
    let q : SourceState := ⟨⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.live.body},parents,s⟩,w,es⟩,stack⟩,none⟩
    advance B K (programs P) resources encode H values ((prefix B H).steps q) q = (prefix B H).after q :=
  certified (PV_THR2_ThreadFields.carrier (PV_THR2_ScopeLiterals.carrier C)) b K P resources encode H values _

#print axioms segments
#print axioms prefix
#print axioms certified
#print axioms history
end PV_LIB_A_F6To15Fixed14
'''
Path('lean/PV_LIB_A_F6To15Fixed14.lean').write_text(s)
