import XSa_PointRun
import XSa_OptionFold
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XSa_DotRun
set_option autoImplicit false
namespace XSa_PointList
abbrev Seven := XRy_ClaimSumStep.Seven

def step {H : Type} (sem : C.Sem H) (s : Slice U8) (g : Coeff)
 (xs : List C.E) (point : Nat) : Result (Option (List C.E)) := do
 let part ← XRn_Join_preparedPart (es sem) s g point
 ok (part.map (fun v => xs++[v]))

def finish (inactive : C.E) (k : Seven) : Option (List C.E) → Result (Option C.E)
 | none => ok none
 | some xs => do
   let out ← (k.val.zip (inactive::xs)).foldlM XSa_ClaimPairs.addTerm XRy_Powers.zero
   ok (some out)

theorem paired {H : Type} (sem : C.Sem H) (s : Slice U8) (g : Coeff) (k : Seven)
 (inactive : C.E) (n : Nat) (i : Usize) (parts : Seven) (xs : List C.E)
 (remaining : i.val+n=6) (hprefix : parts.val.take (i.val+1)=inactive::xs) :
 XSa_PointRun.run sem s g k n i parts =
 (do let ys ← XSa_OptionFold.run (step sem s g) (List.range' i.val n) xs
     finish inactive k ys) := by
 induction n generalizing i parts xs with
 | zero =>
   rw [List.take_of_length_le (by rw [parts.property];omega)] at hprefix
   simp only [XSa_PointRun.run,XSa_OptionFold.run,bind_tc_ok,finish,hprefix]
 | succ n ih =>
   have hi : i.val<6 := by omega
   simp only [XSa_PointRun.run,List.range'_succ,XSa_OptionFold.run,step,bind_assoc_eq]
   apply (bind_eq_iff _ _ _).mpr
   intro opt hpart
   cases opt with
   | none => simp only [Option.map_none,bind_tc_ok,finish]
   | some v =>
     simp only [Option.map_some,bind_tc_ok]
     obtain ⟨j,ej,hj⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=i) (y:=1#usize) (by scalar_tac))
     have hjv : j.val=i.val+1 := by scalar_tac
     have hj7 : j.val<7 := by omega
     have hp : (parts.set j v).val.take (j.val+1)=inactive::(xs++[v]) := by
       rw [XSa_ArrayPrefix.write parts j v hj7,hjv,hprefix]
       rfl
     rw [ej,bind_tc_ok,XSa_ArraySeven.update parts j v hj7,bind_tc_ok,
       ih j (parts.set j v) (xs++[v]) (by omega) hp]
     simp only [hjv]

#print axioms paired
end XSa_PointList
