import NMT_R2_ResultTry
import NMT_R2_EmittedData
set_option autoImplicit false
noncomputable section
namespace NMT_R2_CaptureTry
open Aeneas Aeneas.Std NMT_345 RSL NMT_R2_EmittedData

/-- One emitted `?` occurrence, with complete outer and inner Results and no
invented stopped post-state. Continuation facts are reached-case facts only. -/
theorem source {A B C D : Type} (f : A → C) (g : B → D)
 (r : NMT_R2_ResultTry.R A) (next : A → NMT_R2_ResultTry.R B)
 (m : RS C) (suffix : C → RS D) (env : Env)
 (first : m env (observe f r))
 (later : ∀ a, r = .ok (.Ok a) → suffix (f a) env (observe g (next a))) :
 RS.bind m suffix env (observe g (NMT_R2_ResultTry.bind r next)) := by
 cases r with
 | fail e => exact Or.inr (Or.inl ⟨[],first,rfl⟩)
 | div => exact Or.inr (Or.inr ⟨[],first,rfl⟩)
 | ok value =>
  cases value with
  | Err e => exact Or.inl ⟨.error (pe e),[],⟨.ret (.error (pe e)),[]⟩,first,rfl,rfl⟩
  | Ok a =>
   exact Or.inl ⟨.ok (f a),[],observe g (next a),first,later a rfl,rfl⟩
#print axioms source
end NMT_R2_CaptureTry
end
