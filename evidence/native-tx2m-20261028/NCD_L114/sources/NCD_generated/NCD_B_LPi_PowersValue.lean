-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_LPi_PowersPrefix
set_option autoImplicit false
namespace AspisR1.LPi_PowersValue
open Aeneas Aeneas.Std Result ControlFlow LPi_FieldValues LPi_PowersPrefix

theorem loop {N : Usize} (x p : NE) (a : Array NE N) (i : Usize)
    (hx : canonE x) (hp : canonE p) (hi : i.val ≤ N.val)
    (vp : ew p=power (ew x) i.val) (pref : Holds a (ew x) i.val) :
    ∃ out, FIo_Native.weights.powers_loop x a p i=ok out ∧ Holds out (ew x) N.val := by
  let inv : (Array NE N × NE × Usize) → Prop := fun s =>
    s.2.2.val ≤ N.val ∧ canonE s.2.1 ∧ ew s.2.1=power (ew x) s.2.2.val ∧
      Holds s.1 (ew x) s.2.2.val
  have spec : WP.spec (FIo_Native.weights.powers_loop x a p i)
      (fun out => Holds out (ew x) N.val) := by
    unfold FIo_Native.weights.powers_loop
    apply loop.spec_decr_nat (fun s : Array NE N × NE × Usize => N.val-s.2.2.val)
      inv (fun out => Holds out (ew x) N.val)
      (fun s => FIo_Native.weights.powers_loop.body x s.1 s.2.1 s.2.2) (a,p,i)
    · rintro ⟨arr,pow,index⟩ h
      rcases h with ⟨bound,canonical,value,pref⟩
      change index.val ≤ N.val at bound
      change canonE pow at canonical
      change ew pow=power (ew x) index.val at value
      change Holds arr (ew x) index.val at pref
      by_cases more : index.val < N.val
      · obtain ⟨next,inc,last|cont⟩ := LPi_PowersStep.step x pow arr index more hx canonical
        · rcases last with ⟨he,call⟩
          rw [call,WP.spec_ok]
          have donePref := advance arr (ew x) index pow more pref canonical value
          have hn : index.val+1=N.val := by rw [←inc,he]
          simpa only [hn] using donePref
        · rcases cont with ⟨hne,newPow,call,newCanon,newValue⟩
          rw [call,WP.spec_ok]
          have nextBound : next.val ≤ N.val := by omega
          have nextValue : ew newPow=power (ew x) next.val := by
            rw [newValue,value,inc]
            rfl
          have nextPref : Holds (arr.set index pow) (ew x) next.val := by
            rw [inc]
            exact advance arr (ew x) index pow more pref canonical value
          change (next.val ≤ N.val ∧ canonE newPow ∧
            ew newPow=power (ew x) next.val ∧ Holds (arr.set index pow) (ew x) next.val) ∧
            N.val-next.val < N.val-index.val
          exact ⟨⟨nextBound,newCanon,nextValue,nextPref⟩,by omega⟩
      · rw [LPi_PowersStep.done x pow arr index (by omega),WP.spec_ok]
        have same : index.val=N.val := by omega
        simpa only [same] using pref
    · exact ⟨hi,hp,vp,pref⟩
  exact WP.spec_imp_exists spec

#print axioms loop
end AspisR1.LPi_PowersValue
