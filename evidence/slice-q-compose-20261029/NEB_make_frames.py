from pathlib import Path
E=Path(__file__).resolve().parent
s='''import NEB_AdditiveComposed
import NEB_WideSubRef
set_option autoImplicit false
namespace NEB_AdditiveFrames
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NEB_ArrayRefs
'''
items=[]
for stem,ty,canon,enc,namespace in [('m','U32',lambda n:n+'.val<2147483647',lambda n:n,'M31'),('cm','NC',lambda n:'canonC '+n,lambda n:'wordsC '+n,'CM31'),('qm','NQ',lambda n:'canonQ '+n,lambda n:'wordsQ '+n,'QM31'),('wide','NE',lambda n:'canonE '+n,lambda n:'wordsE '+n,'wide_exact.WideExact')]:
 for op in ['add','sub','double']:
  if (stem=='qm' and op=='double') or (stem=='wide' and op in ['sub','double']):continue
  name=stem+'_'+op;params=f'(x : {ty})' if op=='double' else f'(x y : {ty})'
  hy='' if op=='double' else f' (hy : {canon("y")})';args='x' if op=='double' else 'x y';dom='hx' if op=='double' else 'hx hy'
  model=f'FIo_Native.aspis_core.field.{namespace}.{op} {args}'
  refname=('add' if op=='double' else op)+({'m':'_word','cm':'2','qm':'4','wide':'8'}[stem])
  ref=f'NEB_AdditiveRef.{refname} ({enc("x")}) ({enc("x" if op=="double" else "y")})'
  s+=f'''\ntheorem {name} {{S Event : Type}} (state : S) {params} (hx : {canon("x")}){hy} :
    ∃ z, {model}=ok z ∧
      {ref}=ok ({enc("z")}) ∧ {canon("z")} ∧
      NEB_PureFrame.run (Event:=Event) state ({model})=ok (z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state ({ref})=ok ({enc("z")},state,[]) := by
  obtain ⟨z,run,reference,canonical⟩ := NEB_AdditiveComposed.{name} {args} {dom}
  exact ⟨z,run,reference,canonical,NEB_PureFrame.successful state _ _ run,
    NEB_PureFrame.successful state _ _ reference⟩
'''
  items.append(name)
s+='''
theorem wide_sub {S Event : Type} (state : S) (x y : NE) (hx : canonE x) (hy : canonE y) :
    ∃ z : NE,
      AspisR1CurrentWide.field.wide_exact.WideExact.sub
        (NBG_GetterPorts.wide x) (NBG_GetterPorts.wide y)=ok (NBG_GetterPorts.wide z) ∧
      NEB_AdditiveRef.sub8 (wordsE x) (wordsE y)=ok (wordsE z) ∧ canonE z ∧
      NEB_PureFrame.run (Event:=Event) state (AspisR1CurrentWide.field.wide_exact.WideExact.sub
        (NBG_GetterPorts.wide x) (NBG_GetterPorts.wide y))=ok (NBG_GetterPorts.wide z,state,[]) ∧
      NEB_PureFrame.run (Event:=Event) state (NEB_AdditiveRef.sub8 (wordsE x) (wordsE y))=
        ok (wordsE z,state,[]) := by
  obtain ⟨z,run,reference,canonical⟩ := NEB_WideSubRef.result x y hx hy
  exact ⟨z,run,reference,canonical,NEB_PureFrame.successful state _ _ run,
    NEB_PureFrame.successful state _ _ reference⟩
'''
items.append('wide_sub')
s+='\n'.join('#print axioms '+n for n in items)+'\nend NEB_AdditiveFrames\n';(E/'NEB_AdditiveFrames.lean').write_text(s)
