import NJB_StubLaws
set_option autoImplicit false
namespace AspisR1.NJB_Words
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
/-- The four native log limbs in c0.a,c0.b,c1.a,c1.b order. -/
def word (q : NQ) (i : Fin 4) : U32 :=
 match i.val with | 0=>q.c0.a | 1=>q.c0.b | 2=>q.c1.a | _=>q.c1.b
def value (w : Fin 4 → U32) : NQ := ⟨⟨w 0,w 1⟩,⟨w 2,w 3⟩⟩
theorem value_word (q : NQ) : value (word q)=q := by
 cases q with | mk a b => cases a;cases b;rfl
theorem word_value (w : Fin 4 → U32) : word (value w)=w := by
 funext i
 fin_cases i <;> rfl
theorem ext (x y : NQ) (same : ∀ i,word x i=word y i) : x=y := by
 rw [←value_word x,←value_word y]
 exact congrArg value (funext same)
#print axioms value_word
#print axioms word_value
#print axioms ext
end AspisR1.NJB_Words
