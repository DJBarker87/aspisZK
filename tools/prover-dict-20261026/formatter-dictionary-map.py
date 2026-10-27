from pathlib import Path
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/PDict_FormatterDictionaryMap.lean'
s='''import R1Z.PDict_FormatterTraitMap2
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FormatterDictionaryMap
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterTraitMap PDict_FormatterTraitMap2

def resultMap {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

def innerMap {A B E : Type} (f : A → B) : core.result.Result A E → core.result.Result B E
  | .Ok x => .Ok (f x)
  | .Err e => .Err e

def vecMap {A B : Type} (f : A → B) (v : alloc.vec.Vec A) : alloc.vec.Vec B :=
  ⟨v.val.map f, by simpa only [List.length_map] using v.property⟩

/-- Retypes an arbitrary extracted dictionary. The unreachable Formatter
callback diverges. Every other operation is retained through structural maps;
no native callback correctness or native Formatter representation is asserted. -/
@[reducible] def selected (base : ExternalTypes) (F : Type)
    (ops : @ExternalFuns base) : @ExternalFuns (types base F) :=
  letI : ExternalTypes := types base F
  {
'''
rhs={85:'fun _ _ => .div',16:'fun _ _ _ => .div',
212:'fun inst deflt update marker self => ops.op212 (unFixed base F _ _ _ inst) deflt update marker self',
213:'fun inst deflt update marker asref self data => ops.op213 (unFixed base F _ _ _ inst) deflt update marker asref self data',
214:'fun inst deflt update marker => ops.op214 (unFixed base F _ _ _ inst) deflt update marker',
215:'fun inst less nonzero state out => ops.op215 (unFixedCore base F _ _ _ _ _ _ _ _ _ inst) less nonzero state out',
216:'fun inst update less nonzero state data => ops.op216 (unBufferUser base F _ _ _ _ inst) (unUpdate base F _ _ _ update) less nonzero state data',
217:'fun deflt inst less nonzero db dk => ops.op217 deflt (unBufferUser base F _ _ _ _ inst) less nonzero db dk',
218:'fun {T OutSize} O {B A OS OA K KB KA R Arr L M} inst a b c d e => ops.op218 O (unVariable base F _ _ _ _ _ _ _ _ _ inst) a b c d e',
219:'fun inst a b c d e state buffer out => ops.op219 (unVariable base F _ _ _ _ _ _ _ _ _ inst) a b c d e state buffer out',
220:'fun inst a b c d e state blocks => ops.op220 (unVariable base F _ _ _ _ _ _ _ _ _ inst) a b c d e state blocks',
224:'fun x n g k => @ExternalFuns.op224 base ops (untrace base F x) n g k',
225:'fun x => resultMap (late base F) (@ExternalFuns.op225 base ops (unpublic base F x))',
226:'fun x => @ExternalFuns.op226 base ops (unpublic base F x)',
227:'fun x a b c => @ExternalFuns.op227 base ops (unpublic base F x) a b c',
228:'resultMap (innerMap (vecMap (link base F))) (@ExternalFuns.op228 base ops)',
229:'fun x y => @ExternalFuns.op229 base ops (unlate base F x) (unlate base F y)',
232:'fun x => resultMap (fun r => (r.1,times base F r.2)) (@ExternalFuns.op232 base ops x)'}
for i in range(262):s+=f'    op{i} := {rhs.get(i,f"ops.op{i}")}\n'
s+='  }\n'
s+='''
theorem kind_retained (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    (selected base F ops).op23 = ops.op23 := rfl

theorem formatter_erased (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base)
    (e : aspis_core.r0.Error) (fmt : F) :
    (selected base F ops).op85 e fmt = .div := rfl

#print axioms kind_retained
#print axioms formatter_erased
end R1Z.PDict_FormatterDictionaryMap
'''
p.write_text(s)
