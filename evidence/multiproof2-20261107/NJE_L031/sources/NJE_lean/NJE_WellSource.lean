import NJE_AllAdapter

set_option autoImplicit false
noncomputable section
namespace NJE_WellSource
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable

def order (s : Slice U32) : Bool :=
 decide ((s.val[0]!).val < (s.val[1]!).val)
def domain (x : U32) : Bool := decide (x.val<262144)

def allValues {α : Type} (p : α → Bool) (xs : List α) : Result Bool := do
 let (b,_) ← NFU_Retarget.core.iter.traits.iterator.Iterator.all.default
   (NJE_AllAdapter.listInst α) (NJE_AllAdapter.predicate p) xs ()
 ok b

theorem all_result {α : Type} (p : α → Bool) (xs : List α) :
    allValues p xs=ok (xs.all p) := by
 obtain ⟨tail,h⟩ := NJE_AllAdapter.default_all p xs
 simp only [allValues,h,bind_tc_ok]
 rfl

def emitted (xs : List U32) : Result Bool := do
 if xs.isEmpty then ok false else
 if xs.length≤16 then
   let ordered ← allValues order (NJA_WellIteration.windows xs)
   if ordered then allValues domain xs else ok false
 else ok false

theorem order_pair (a b : U32) : order (NJA_WellPredicateLaws.pair a b)=decide (a.val<b.val) := by
 simp [order,NJA_WellPredicateLaws.pair]

theorem order_all (xs : List U32) :
    (NJA_WellIteration.windows xs).all order =
      decide (NJA_WellFormed.adjacent (xs.map (fun x : U32 => x.val))) := by
 induction xs with
 | nil => simp [NJA_WellIteration.windows,List.all,NJA_WellFormed.adjacent]
 | cons x xs ih =>
   cases xs with
   | nil => simp [NJA_WellIteration.windows,List.all,NJA_WellFormed.adjacent]
   | cons y ys =>
     simp only [NJA_WellIteration.windows,List.all_cons,order_pair,List.map_cons,
       NJA_WellFormed.adjacent,ih]
     by_cases h : x.val<y.val <;> simp [h]

theorem domain_all (xs : List U32) : xs.all domain=decide (∀ x∈xs,x.val<262144) := by
 apply Bool.eq_iff_iff.mpr
 simp [domain]

theorem source (xs : List U32) :
    emitted xs=ok (NJA_WellFormed.source (xs.map (fun x : U32 => x.val))) := by
 unfold emitted NJA_WellFormed.source
 rw [all_result,order_all]
 simp only [bind_tc_ok,List.map_eq_nil_iff,List.length_map]
 by_cases e : xs=[]
 · simp [e]
 · by_cases small : xs.length≤16
   · by_cases sorted : NJA_WellFormed.adjacent (xs.map (fun x : U32 => x.val))
     · simp [e,small,sorted,all_result,domain_all,show ¬xs.length>16 by omega]
     · simp [e,small,sorted]
   · simp [e,small,show xs.length>16 by omega]

#print all_result
#print axioms all_result
#print order_pair
#print axioms order_pair
#print order_all
#print axioms order_all
#print domain_all
#print axioms domain_all
#print source
#print axioms source
end NJE_WellSource
end
