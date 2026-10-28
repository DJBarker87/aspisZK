import R1Z.PV_Src_PortField
import R1Z.PV_RunJoin_ForestEquality30
import R1Z.PV_Src_CompilerTactic
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ZeroScan31
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderAdmissionStd
local instance (p : Prop) : Decidable p := Classical.propDecidable p
abbrev predicate := pool_v1.pair_tree_profile.PoolV1PairLeafWitnessV1.validate.closure.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool
variable {K : Type} [Field K] [CharP K 2147483647]

theorem word_zero (m : U32)
    (h : core.cmp.PartialEq.ne.trait_default aspis_core.field.M31.Insts.CoreCmpPartialEqM31 m
      aspis_core.field.M31.ZERO = ok false) : m = 0#u32 := by
  rw [PV_RunJoin_ForestEquality30.dictionary,PV_RunJoin_RuntimePrimitives30.word_ne] at h
  simpa only [AspisBuilderAdmissionSource.aspis_core.field.M31.ZERO,
    Result.ok.injEq,decide_eq_false_iff_not,not_not] using h
#print axioms word_zero

theorem scalar (c x : U32) (state : U32)
    (h : predicate.call_mut c x = ok (false,state)) :
    state = c ∧ liftU (K := K) c * liftU x = 0 := by
  change (do let m ← aspis_core.field.M31.mul c x
             let b ← core.cmp.PartialEq.ne.trait_default aspis_core.field.M31.Insts.CoreCmpPartialEqM31 m aspis_core.field.M31.ZERO
             ok (b,c)) = _ at h
  pv_peel h with m hm
  pv_peel h with b hb
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj h)
  have he := word_zero m hb
  obtain ⟨z,hz,_,hv⟩ := PV_Src_PortField.multiply (K := K) c x
  have hez : z=m := Result.ok.inj (hz.symm.trans hm)
  rw [hez,he] at hv
  exact ⟨rfl,hv.symm.trans (by rfl)⟩
#print axioms scalar

theorem list (xs : List U32) (c : U32) (n : Nat)
    (h : scan predicate true xs c = ok (false,n)) :
    ∀ x ∈ xs, liftU (K := K) c * liftU x = 0 := by
  induction xs generalizing c n with
  | nil => simp
  | cons x xs ih =>
    rw [scan] at h
    pv_peel h with pair hp
    rcases pair with ⟨b,state⟩
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte] at h
    · obtain ⟨hs,hx⟩ := scalar (K := K) c x state hp
      subst state
      pv_peel h with tail ht
      rcases tail with ⟨b,n'⟩
      have hb := congrArg Prod.fst (Result.ok.inj h)
      dsimp only at hb
      subst b
      have ht' := ih c n' ht
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact ht' y hy
    · cases h
#print axioms list

theorem array (d : Array U32 8#usize) (c : U32)
    (after : core.slice.iter.Iter U32)
    (h : iterScan predicate true ⟨Array.to_slice d,0⟩ c = ok (false,after)) :
    ∀ j : Fin 8, liftU (K := K) c * digK d j = 0 := by
  unfold iterScan at h
  pv_peel h with pair hp
  rcases pair with ⟨b,n⟩
  have hb := congrArg Prod.fst (Result.ok.inj h)
  dsimp only at hb
  subst b
  have hall := list (K := K) d.val c n (by simpa only [Array.to_slice,List.drop_zero] using hp)
  intro j
  have hlt : j.val < d.val.length := by rw [d.property]; simpa using j.isLt
  change liftU c * liftU d.val[j.val]! = 0
  rw [List.getElem!_eq_getElem hlt]
  exact hall _ (List.getElem_mem hlt)
#print axioms array
end R1Z.PV_RunJoin_ZeroScan31
