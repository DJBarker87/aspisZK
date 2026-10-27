import R1Z.ProverRwFullTypes
namespace R1Z.PV_CBM_PushList
open Aeneas Aeneas.Std Result
set_option autoImplicit false

def pushList {α : Type} : List α → alloc.vec.Vec α → Result (alloc.vec.Vec α)
  | [], out => ok out
  | value::values, out => do
    let next ← alloc.vec.Vec.push out value
    pushList values next

theorem wp_exists {α : Type} (r : Result α) (p : α → Prop) (h : WP.spec r p) :
    ∃ v, r=ok v ∧ p v := by
  cases r <;> simp_all [WP.spec,WP.theta,WP.wp_return]

theorem pushList_spec {α : Type} (values : List α) (out : alloc.vec.Vec α)
    (hc : out.val.length+values.length≤4096) :
    ∃ result, pushList values out=ok result ∧ result.val=out.val++values := by
  induction values generalizing out with
  | nil => exact ⟨out,rfl,by simp⟩
  | cons value values ih =>
    have hlen : out.val.length+values.length+1≤4096 := by
      simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hc
    obtain ⟨next,hnext,hval⟩ := wp_exists _ _
      (alloc.vec.Vec.push_spec out value (by scalar_tac))
    have hn : next.val.length+values.length≤4096 := by
      rw [hval,List.length_append]
      simp only [List.length_singleton]
      omega
    obtain ⟨result,hresult,hrval⟩ := ih next hn
    refine ⟨result,?_,?_⟩
    · rw [pushList,hnext]
      exact hresult
    · rw [hrval,hval,List.append_assoc]
      rfl

#print axioms wp_exists
#print axioms pushList_spec
end R1Z.PV_CBM_PushList
