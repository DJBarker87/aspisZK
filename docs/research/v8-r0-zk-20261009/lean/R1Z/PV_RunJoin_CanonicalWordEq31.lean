import R1Z.BuilderRecordCanonical
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CanonicalWordEq31
open Aeneas Aeneas.Std R0Z.WriterRefine R1J.SpendWitnessMap
variable {K : Type} [Field K] [CharP K 2147483647]

theorem word (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647)
    (h : liftU (K := K) a = liftU b) : a=b := by
  have hf : liftU (K := F) a = liftU b := by
    apply (ι : F →+* K).injective
    simpa only [liftU,map_natCast] using h
  have hn := congrArg (fun x : F => x.val) hf
  change (a.val : ZMod 2147483647).val = (b.val : ZMod 2147483647).val at hn
  rw [ZMod.val_natCast,ZMod.val_natCast,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at hn
  exact UScalar.eq_of_val_eq hn
#print axioms word

theorem digest (a b : Array U32 8#usize) (ha : Canon8 a) (hb : Canon8 b)
    (h : digK (K := K) a = digK b) : a=b := by
  apply BuilderRecordCanonical.array_ext
  intro j hj
  have hj8 : j<8 := by simpa only [UScalar.ofNatCore_val_eq] using hj
  apply word (K := K) _ _ (ha j hj8) (hb j hj8)
  exact congrFun h ⟨j,hj8⟩
#print axioms digest

theorem frontier (a b : Array (Array U32 8#usize) 20#usize)
    (ha : ∀ j : Fin 20, Canon8 a.val[j.val]!)
    (hb : ∀ j : Fin 20, Canon8 b.val[j.val]!)
    (h : ∀ j : Fin 20, digK (K := K) a.val[j.val]! = digK b.val[j.val]!) : a=b := by
  apply BuilderRecordCanonical.array_ext
  intro j hj
  have hj20 : j<20 := by simpa only [UScalar.ofNatCore_val_eq] using hj
  exact digest (K := K) _ _ (ha ⟨j,hj20⟩) (hb ⟨j,hj20⟩) (h ⟨j,hj20⟩)
#print axioms frontier
end R1Z.PV_RunJoin_CanonicalWordEq31
