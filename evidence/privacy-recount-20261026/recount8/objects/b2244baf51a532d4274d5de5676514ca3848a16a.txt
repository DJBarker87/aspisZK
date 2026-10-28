import R1Z.ProverRwSuccessWideSource
set_option autoImplicit false
namespace R1Z.ProverRwSuccessArrayFromFn
open Aeneas Aeneas.Std Result
-- Same ordered FnMut model as BuilderStdModels; no native-library adequacy claim.
def run {T C : Type} (f : core.ops.function.FnMut C Usize T) :
    List Usize → C → Result (List T × C)
  | [],c => .ok ([],c)
  | i::is,c => do
    let (x,c') ← f.call_mut c i
    let (xs,c'') ← run f is c'
    .ok (x::xs,c'')
def indices (n : Usize) : List Usize :=
  List.ofFn (fun i : Fin n.val => Usize.ofNatCore i.val (lt_trans i.isLt n.hBounds))
def fromFn {T C : Type} (n : Usize) (f : core.ops.function.FnMut C Usize T) (c : C) :
    Result (Array T n) := do
  let (xs,_) ← run f (indices n) c
  (if h : xs.length=n.val then .ok ⟨xs,h⟩ else .fail .panic)

theorem run_pure {T C : Type} (f : core.ops.function.FnMut C Usize T)
    (g : Usize → T) (c : C) (is : List Usize)
    (calls : ∀ i∈is, f.call_mut c i=.ok (g i,c)) :
    run f is c=.ok (is.map g,c) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [run,calls i (by simp),bind_tc_ok]
    change (do let (xs,c'') ← run f is c; .ok (g i::xs,c''))=
      .ok (g i::is.map g,c)
    rw [ih (fun j hj => calls j (by simp [hj]))]
    rfl

theorem fromFn_pure {T C : Type} (n : Usize) (f : core.ops.function.FnMut C Usize T)
    (g : Usize → T) (c : C) (calls : ∀ i, i.val<n.val → f.call_mut c i=.ok (g i,c)) :
    ∃ a, fromFn n f c=.ok a ∧ a.val=(indices n).map g := by
  have hh : ∀ i∈indices n, f.call_mut c i=.ok (g i,c) := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := List.mem_ofFn.mp hi
    exact calls _ j.isLt
  have len : ((indices n).map g).length=n.val := by simp [indices]
  refine ⟨⟨(indices n).map g,len⟩,?_,rfl⟩
  unfold fromFn
  rw [run_pure f g c _ hh]
  simp only [bind_tc_ok]
  change (if h : ((indices n).map g).length=n.val then
    Result.ok (⟨(indices n).map g,h⟩ : Array T n) else Result.fail Error.panic)=
    Result.ok (⟨(indices n).map g,len⟩ : Array T n)
  rw [dif_pos len]
#print axioms run_pure
#print axioms fromFn_pure
end R1Z.ProverRwSuccessArrayFromFn
