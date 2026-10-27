import PV_B3_PolynomialEmission
import PV_B3_CanonicalIndexTotal
import PV_B3_CanonicalMReduce
import PV_B3_CanonicalSub
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_Copy_117
set_option autoImplicit false
 theorem reconstruct_component (xs : Array U64 3#usize) :
    ∃ z, host_arithmetic.reconstruct_component xs = ok z ∧ C z := by
  obtain ⟨a,ha⟩ := index_total xs 0#usize (by decide)
  obtain ⟨b,hb⟩ := index_total xs 1#usize (by decide)
  obtain ⟨c,hc⟩ := index_total xs 2#usize (by decide)
  obtain ⟨m0,h0,c0⟩ := current_mreduce a
  obtain ⟨m1,h1,c1⟩ := current_mreduce b
  obtain ⟨m2,h2,c2⟩ := current_mreduce c
  obtain ⟨d,hd,cd⟩ := current_sub m0 m1 c0 c1
  obtain ⟨e,he,ce⟩ := current_sub m2 m0 c2 c0
  obtain ⟨f,hf,cf⟩ := current_sub e m1 ce c1
  refine ⟨⟨d,f⟩,?_,cd,cf⟩
  simp only [host_arithmetic.reconstruct_component,ha,hb,hc,h0,h1,h2,hd,he,hf,bind_tc_ok]
#print axioms reconstruct_component
end PV_B3_Canonical
