import NDN_PackedFrame
set_option autoImplicit false
namespace NDN_FieldAppendInduction
variable {α β : Type}

def run (canonical : α → Bool) (bytes : α → List β) (out : List β) : List α → Bool × List β
 | [] => (true,out)
 | w::ws => if canonical w then run canonical bytes (out++bytes w) ws else (false,out)

theorem accepted (canonical : α → Bool) (bytes : α → List β) (out : List β)
 (words : List α) (hc:∀ w∈words,canonical w=true) :
 run canonical bytes out words=(true,out++words.flatMap bytes) := by
 induction words generalizing out with
 | nil => simp only [run,List.flatMap_nil,List.append_nil]
 | cons w ws ih =>
   have hw : canonical w=true := hc w (by simp)
   have hs : ∀ v∈ws,canonical v=true := by intro v hv;exact hc v (by simp [hv])
   simp only [run,hw,ite_true,ih _ hs,List.flatMap_cons,List.append_assoc]

theorem rejected (canonical : α → Bool) (bytes : α → List β) (out : List β)
 (front : List α) (bad : α) (suffix : List α)
 (hp:∀ w∈front,canonical w=true) (hb:canonical bad=false) :
 run canonical bytes out (front++bad::suffix)=(false,out++front.flatMap bytes) := by
 induction front generalizing out with
 | nil => simp [run,hb]
 | cons w ws ih =>
   have hw : canonical w=true := hp w (by simp)
   have hs : ∀ v∈ws,canonical v=true := by intro v hv;exact hp v (by simp [hv])
   simp only [List.cons_append,run,hw,ite_true,ih _ hs,List.flatMap_cons,List.append_assoc]

#print axioms accepted
#print axioms rejected
end NDN_FieldAppendInduction
