import NGA_Accumulate
set_option autoImplicit false
namespace NGA_SumAlgebra
open Aeneas Aeneas.Std Result NGA_Cell NGA_Converter NGA_PreparePairs

def sumProducts (xs : List Input) : NGA_Converter.Q :=
 (xs.map (fun p => NGA_ChannelAlgebra.decodeQ p.1*NGA_ChannelAlgebra.decodeQ p.2)).sum

theorem channels (xs : List Input) (cs : List Pair)
 (canonical : ∀ x∈xs, Canonical x.1 ∧ Canonical x.2)
 (assoc : List.Forall₂ PairFor xs cs) :
 interpret (fun d => (NGA_Small.terms cs d : M))=sumProducts xs := by
 induction assoc with
 | nil => simpa only [NGA_Small.terms,List.map_nil,List.sum_nil,sumProducts,Nat.cast_zero] using NGA_ChannelAlgebra.zero
 | @cons x p xs ps hp h ih =>
   have hx := canonical x (by simp)
   have tail := ih (by intro q hq;exact canonical q (by simp [hq]))
   have state : (fun d => (NGA_Small.terms (p::ps) d : M))=
     fun d => NGA_ChannelAlgebra.channels x.1 d*NGA_ChannelAlgebra.channels x.2 d+
       (NGA_Small.terms ps d : M) := by
     funext d
     simp only [NGA_Small.terms,List.map_cons,List.sum_cons,Nat.cast_add,NGA_Nine.product,Nat.cast_mul]
     rw [NGA_CacheValues.source x.1 hx.1 p.1 hp.1 d,NGA_CacheValues.source x.2 hx.2 p.2 hp.2.1 d]
   rw [state,NGA_ChannelAlgebra.add,NGA_ChannelAlgebra.product,tail]
   rfl

theorem source (xs : List Input) (arity : xs.length≤4)
 (canonical : ∀ x∈xs, Canonical x.1 ∧ Canonical x.2) :
 ∃ out, NGA_SmallResult.sourceModel xs=ok out ∧ Canonical out ∧
   AspisR1.PoseidonPreparedKaratsubaValue.decodeQM out=sumProducts xs := by
 obtain ⟨cs,sums,out,_,assoc,_,_,values,hr,hc,ho⟩ := NGA_SmallResult.source xs arity canonical
 obtain ⟨out',hr',_,hv⟩ := NGA_Converter.value sums
 have same : out'=out := Result.ok.inj (hr'.symm.trans hr)
 subst out'
 refine ⟨out,ho,hc,?_⟩
 rw [hv]
 have state : decode sums=fun d => (NGA_Small.terms cs d : M) := by
   funext d;change ((get sums d).val : M)=_;rw [values]
 rw [state]
 exact channels xs cs canonical assoc

#print axioms channels
#print axioms source
end NGA_SumAlgebra
