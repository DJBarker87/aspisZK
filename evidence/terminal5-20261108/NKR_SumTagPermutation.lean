import NJL_TagData
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumTagPermutation
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
def base : Nat := 1124073472
def tag (t : Fin 272) : Nat := (NJL_TagData.tag t).val
def side (t : Fin 272) : Bool := decide (136≤t.val)
/-- Exact tag-domain assertion in NKR_tag_metadata_cut. -/
def Domain : Prop := ∀ t,base≤tag t ∧ tag t<base+136
/-- Exact NKR_tag_permutation_cut assertion:two fixed-registry positions with
SAME tag and producer/consumer side are identical. This is a reviewed native
constant-metadata cut,not a field/output/cohort equality. -/
def Cut : Prop := ∀ (t u : Fin 272),tag t=tag u → side t=side u → t=u

def index (domain : Domain) (t : Fin 272) : Fin 136 :=
 ⟨tag t-base,by have h:=domain t;omega⟩
def encoded (domain : Domain) (t : Fin 272) : Fin 272 :=
 ⟨(index domain t).val+(if side t then 136 else 0),by
   have h:=(index domain t).isLt
   split <;> omega⟩

theorem injective (domain : Domain) (cut : Cut) : Function.Injective (encoded domain) := by
 intro t u eq
 have val := congrArg Fin.val eq
 change (index domain t).val+(if side t then 136 else 0)=
  (index domain u).val+(if side u then 136 else 0) at val
 have ht:=(index domain t).isLt
 have hu:=(index domain u).isLt
 have st : side t=side u := by
  cases hst : side t <;> cases hsu : side u <;> simp only [hst,hsu,if_true,if_false,Bool.false_eq_true,Bool.true_eq_true] at val ⊢ <;> omega
 have vals : (index domain t).val=(index domain u).val := by rw [st] at val;omega
 have tags : tag t=tag u := by
  change tag t-base=tag u-base at vals
  have dt:=domain t
  have du:=domain u
  omega
 exact cut t u tags st

/-- Finite self-map pigeonhole:272registry positions cover exactly the
136producer plus136consumer source entries. No272-cell kernel replay. -/
theorem surjective (domain : Domain) (cut : Cut) : Function.Surjective (encoded domain) :=
 Finite.surjective_of_injective (encoded domain) (injective domain cut)

theorem sum_transport (domain : Domain) (cut : Cut) (f : Fin 272 → K) :
 ((List.finRange 272).map (fun t=>f (encoded domain t))).sum=((List.finRange 272).map f).sum := by
 change ((List.ofFn (fun t : Fin 272=>t)).map (fun t=>f (encoded domain t))).sum=
  ((List.ofFn (fun t : Fin 272=>t)).map f).sum
 simp only [List.map_ofFn,List.sum_ofFn]
 refine Finset.sum_bij (fun t _=>encoded domain t) ?_ ?_ ?_ ?_
 · intro t ht
   exact Finset.mem_univ _
 · intro t ht u hu eq
   exact injective domain cut eq
 · intro u hu
   obtain ⟨t,eq⟩ := surjective domain cut u
   exact ⟨t,Finset.mem_univ _,eq⟩
 · intro t ht
   rfl

#print axioms injective
#print axioms surjective
#print axioms sum_transport
end AspisR1.NKR_SumTagPermutation
end
