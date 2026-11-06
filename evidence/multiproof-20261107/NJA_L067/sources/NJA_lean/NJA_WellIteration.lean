import NJA_WellPredicateLaws
import NJA_WellFormed
import NDD_WellformedModel

set_option autoImplicit false
noncomputable section
namespace NJA_WellIteration
open Aeneas Aeneas.Std Result NJA_Multiproof
attribute [local instance] Classical.propDecidable

def windows : List U32 → List (Slice U32)
 | [] => []
 | [_] => []
 | x::y::xs => NJA_WellPredicateLaws.pair x y :: windows (y::xs)

def order (w : Slice U32) : Result Bool := do
 let (b,_) ← multiproof.well_formed.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool.call_mut () w
 ok b

def domain (x : U32) : Result Bool := do
 let (b,_) ← multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool.call_mut () x
 ok b

theorem domain_total (x : U32) : domain x = ok (decide (x.val < 262144)) := by
 simp only [domain,NJA_WellPredicateLaws.domain,bind_tc_ok]
 rfl

theorem order_pair (a b : U32) : order (NJA_WellPredicateLaws.pair a b) = ok (decide (a.val<b.val)) := by
 simp only [order,NJA_WellPredicateLaws.order,bind_tc_ok]
 rfl

theorem domain_all (xs : List U32) :
 xs.allM domain = ok (decide (∀ x ∈ xs, x.val<262144)) := by
 rw [NDD_WellformedModel.allM_total domain (fun x => decide (x.val<262144)) domain_total]
 congr 1
 apply Bool.eq_iff_iff.mpr
 simp

theorem order_all (xs : List U32) :
 (windows xs).allM order = ok (decide (NJA_WellFormed.adjacent (xs.map (fun x : U32 => x.val)))) := by
 induction xs with
 | nil => simp [windows,List.allM,NJA_WellFormed.adjacent]; rfl
 | cons x xs ih =>
   cases xs with
   | nil => simp [windows,List.allM,NJA_WellFormed.adjacent]; rfl
   | cons y ys =>
     simp only [windows,List.allM,order_pair,List.map_cons,NJA_WellFormed.adjacent,bind_tc_ok]
     by_cases h : x.val<y.val
     · simp [h,ih]
     · simp [h]
       rfl

def guarded (xs : List U32) : Result Bool := do
 if xs.isEmpty then ok false else
 if xs.length ≤ 16 then
   let b ← (windows xs).allM order
   if b then xs.allM domain else ok false
 else ok false

theorem result (xs : List U32) :
 guarded xs = ok (NJA_WellFormed.source (xs.map (fun x : U32 => x.val))) := by
 unfold guarded NJA_WellFormed.source
 rw [order_all]
 simp only [bind_tc_ok,List.map_eq_nil_iff,List.length_map]
 by_cases e : xs=[]
 · simp [e]
 · by_cases large : xs.length≤16
   · by_cases a : NJA_WellFormed.adjacent (List.map (fun x : U32 => x.val) xs)
     · simp [e,large,a,domain_all,show ¬xs.length>16 by omega]
     · simp [e,large,a]
   · simp [e,large,show xs.length>16 by omega]

#print axioms domain_total
#print axioms order_pair
#print axioms domain_all
#print axioms order_all
#print axioms result
end NJA_WellIteration
end
