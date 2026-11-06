import NJB_StubLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_StateUpdates
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
variable {I : Type} [DecidableEq I]
def canonical (s : I → NQ) : Prop := ∀ i,Canon (s i)
def decoded (s : I → NQ) : I → K := fun i=>decode (s i)
def set (s : I → NQ) (i : I) (x : NQ) : I → NQ := fun j=>if i=j then x else s j
def addModel (s : I → K) (i : I) (x : K) : I → K := fun j=>if i=j then s i+x else s j
def add (s : I → NQ) (i : I) (x : NQ) : Result (I → NQ) := do
 let out ← FIq_Native.field.QM31.add (s i) x
 ok (set s i out)
theorem add_result (s : I → NQ) (i : I) (x : NQ) (hs : canonical s) (hx : Canon x) :
 ∃ out,add s i x=ok out ∧ canonical out ∧ decoded out=addModel (decoded s) i (decode x) := by
 obtain ⟨z,call,hz,vz⟩ := NJB_StubLaws.qm_add (s i) x (hs i) hx
 refine ⟨set s i z,?_,?_,?_⟩
 · simp only [add,call,bind_tc_ok]
 · intro j
   by_cases same : i=j
   · simpa only [set,if_pos same] using hz
   · simpa only [set,if_neg same] using hs j
 · funext j
   by_cases same : i=j <;> simp [decoded,set,addModel,same,vz]
def mulAdd (s : I → NQ) (i : I) (x y : NQ) : Result (I → NQ) := do
 let product ← FIq_Native.field.QM31.mul x y
 add s i product
theorem mul_add_result (s : I → NQ) (i : I) (x y : NQ)
 (hs : canonical s) (hx : Canon x) (hy : Canon y) :
 ∃ out,mulAdd s i x y=ok out ∧ canonical out ∧
 decoded out=addModel (decoded s) i (decode x*decode y) := by
 obtain ⟨p,cp,hp,vp⟩ := NJB_StubLaws.qm_mul x y hx hy
 obtain ⟨out,co,ho,vo⟩ := add_result s i p hs hp
 refine ⟨out,?_,ho,?_⟩
 · simp only [mulAdd,cp,co,bind_tc_ok]
 · simpa only [vp] using vo
def run {α : Type} (step : α → (I → NQ) → Result (I → NQ)) : List α → (I → NQ) → Result (I → NQ)
 | [],s=>ok s
 | x::xs,s=>do let next ← step x s;run step xs next
/-- Generic support interface only: concrete row roots supply child from their
proved same-input field and frame laws; it is never a row-root hypothesis. -/
theorem run_result {α : Type} (step : α → (I → NQ) → Result (I → NQ))
 (model : α → (I → K) → I → K) (xs : List α) (s : I → NQ) (hs : canonical s)
 (child : ∀ x∈xs,∀ before,canonical before→∃ after,step x before=ok after ∧ canonical after ∧
  decoded after=model x (decoded before)) :
 ∃ out,run step xs s=ok out ∧ canonical out ∧
 decoded out=xs.foldl (fun state x=>model x state) (decoded s) := by
 induction xs generalizing s with
 | nil => exact ⟨s,rfl,hs,rfl⟩
 | cons x xs ih =>
   obtain ⟨next,cn,hn,vn⟩ := child x (by simp) s hs
   obtain ⟨out,co,ho,vo⟩ := ih next hn (fun x hx=>child x (by simp [hx]))
   refine ⟨out,?_,ho,?_⟩
   · simp only [run,cn,co,bind_tc_ok]
   · simpa only [List.foldl_cons,vn] using vo
theorem sum_frame {α : Type} (term : α → K) (xs : List α) (s : I → K) (i j : I) :
 (xs.foldl (fun state x=>addModel state i (term x)) s) j=
 if i=j then s i+(xs.map term).sum else s j := by
 induction xs generalizing s with
 | nil => by_cases h : i=j <;> simp [h,addModel]
 | cons x xs ih =>
   rw [List.foldl_cons,ih]
   by_cases h : i=j <;> simp [addModel,h,List.map_cons,List.sum_cons] <;> ring
#print axioms add_result
#print axioms mul_add_result
#print axioms run_result
#print axioms sum_frame
end AspisR1.NJB_StateUpdates
end
