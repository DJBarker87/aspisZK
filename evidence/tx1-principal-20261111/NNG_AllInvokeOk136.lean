import NNG_TraceAll136
set_option autoImplicit false
namespace AspisR1.NNG_AllInvokeOk136
open Aeneas Aeneas.Std Result NMT_CallTree NNG_TraceAll136

theorem invoke_ok {Args A B : Type} (P : Event → Prop) (site : String) (args : Args) (a : A) (k : A → Code B)
    (head : P (.call site args (.ok a))) (tail : All P (k a)) :
    All P (NMT_CallTree.bind (NMT_CallTree.invoke site args (.ok a)) k) := by
  apply NNG_TraceAll136.bind P
  · exact NNG_TraceAll136.invoke P site args (.ok a) head
  · intro value returned
    have same : a=value := Result.ok.inj returned
    subst value
    exact tail
#print axioms invoke_ok
end AspisR1.NNG_AllInvokeOk136
