import JGk_TX2_ComparatorTransport
set_option autoImplicit false
namespace AspisR1.JGk_TX2_KeyInjective

theorem source {α β : Type} (domain xs ys : List α) (key : α → β)
    (distinct : ∀ a ∈ domain, ∀ b ∈ domain, key a=key b → a=b)
    (left : ∀ a ∈ xs, a ∈ domain) (right : ∀ a ∈ ys, a ∈ domain)
    (same : xs.map key=ys.map key) : xs=ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons b bs => cases same
  | cons a as ih =>
    cases ys with
    | nil => cases same
    | cons b bs =>
      have eq := List.cons.inj same
      have ab : a=b := distinct a (left a (by simp)) b (right b (by simp)) eq.1
      subst b
      congr 1
      exact ih bs (fun x hx => left x (List.mem_cons_of_mem a hx))
        (fun x hx => right x (List.mem_cons_of_mem a hx)) eq.2
#print axioms source
end AspisR1.JGk_TX2_KeyInjective
