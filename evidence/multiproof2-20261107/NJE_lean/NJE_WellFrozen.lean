import NJE_AllCalls
import NJE_WellPacket

set_option autoImplicit false
noncomputable section
namespace NJE_WellFrozen
open Aeneas Aeneas.Std Result NJA_Multiproof
attribute [local instance] Classical.propDecidable

def orderFn : core.ops.function.FnMut Unit (Slice U32) Bool :=
 multiproof.well_formed.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU32Bool
def domainFn : core.ops.function.FnMut Unit U32 Bool :=
 multiproof.well_formed.closure_1.Insts.CoreOpsFunctionFnMutTupleSharedU32Bool

theorem window_pair (xs : List U32) :
    ∀ s∈NJA_WellIteration.windows xs, ∃ a b, s=NJA_WellPredicateLaws.pair a b := by
 induction xs with
 | nil => simp [NJA_WellIteration.windows]
 | cons a xs ih =>
   cases xs with
   | nil => simp [NJA_WellIteration.windows]
   | cons b bs =>
     intro s hs
     simp only [NJA_WellIteration.windows,List.mem_cons] at hs
     rcases hs with rfl | hs
     · exact ⟨a,b,rfl⟩
     · exact ih s hs

def allCalls {α : Type} (f : core.ops.function.FnMut Unit α Bool) (xs : List α) : Result Bool := do
 let (b,_) ← NFU_Retarget.core.iter.traits.iterator.Iterator.all.default
   (NJE_AllAdapter.listInst α) f xs ()
 ok b

theorem order_all (xs : List U32) :
    allCalls orderFn (NJA_WellIteration.windows xs)=
      ok ((NJA_WellIteration.windows xs).all NJE_WellSource.order) := by
 obtain ⟨tail,h⟩ := NJE_AllCalls.default_all orderFn NJE_WellSource.order
   (NJA_WellIteration.windows xs) (by
     intro s hs
     obtain ⟨a,b,rfl⟩ := window_pair xs s hs
     simpa only [orderFn,NJE_WellSource.order_pair] using NJA_WellPredicateLaws.order a b ())
 simp only [allCalls,h,bind_tc_ok]
 rfl

theorem domain_all (xs : List U32) :
    allCalls domainFn xs=ok (xs.all NJE_WellSource.domain) := by
 obtain ⟨tail,h⟩ := NJE_AllCalls.default_all domainFn NJE_WellSource.domain xs (by
   intro x hx
   exact NJA_WellPredicateLaws.domain x ())
 simp only [allCalls,h,bind_tc_ok]
 rfl

-- The emitted guards and emitted closures; only the iterator ABI is retargeted.
def emitted (indices : Slice U32) : Result Bool := do
 let empty ← core.slice.Slice.is_empty indices
 let reject ← if empty then ok true else ok (Slice.len indices > 16#usize)
 if reject then ok false else
 let ordered ← allCalls orderFn (NJA_WellIteration.windows indices.val)
 if ordered then allCalls domainFn indices.val else ok false

theorem association (indices : Slice U32) :
    emitted indices=NJE_WellSource.emitted indices.val := by
 simp only [emitted,order_all,domain_all,bind_tc_ok]
 simp only [core.slice.Slice.is_empty,Slice.len,NJE_WellSource.emitted,
   NJE_WellSource.all_result]
 by_cases empty : indices.val=[]
 · simp [empty]
 · by_cases small : indices.val.length≤16
   · simp [empty,small,show ¬indices.val.length>16 by omega]
   · simp [empty,small,show indices.val.length>16 by omega]

theorem TX1_128 (indices : Slice U32) (out : Bool) (calls : Nat)
    (cut : NJE_WellPacket.Cut indices.val (NJE_WellPacket.ordered indices.val)
      (NJE_WellPacket.domain indices.val) out calls) :
    emitted indices=ok out ∧
    out=decide (AspisR1.OraclePortFrozenOrder.wellFormed (indices.val.map (fun x : U32 => x.val))) := by
 rw [association]
 exact NJE_WellPacket.TX1_128 indices.val out calls cut

theorem TX2_094 (indices : Slice U32) (out : Bool) (calls : Nat)
    (cut : NJE_WellPacket.Cut indices.val (NJE_WellPacket.ordered indices.val)
      (NJE_WellPacket.domain indices.val) out calls) :
    emitted indices=ok out ∧
    out=decide (AspisR1.OraclePortFrozenOrder.wellFormed (indices.val.map (fun x : U32 => x.val))) :=
 TX1_128 indices out calls cut

#print window_pair
#print axioms window_pair
#print order_all
#print axioms order_all
#print domain_all
#print axioms domain_all
#print association
#print axioms association
#print TX1_128
#print axioms TX1_128
#print TX2_094
#print axioms TX2_094
end NJE_WellFrozen
end
