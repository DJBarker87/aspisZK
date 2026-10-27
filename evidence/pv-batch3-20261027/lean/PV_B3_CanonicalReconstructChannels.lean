import PV_B3_CanonicalReconstructComponent
import PV_B3_CanonicalHostR
import PV_B3_CanonicalCAdd
import PV_B3_CanonicalCSub
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result PV_B3_Copy_117
set_option autoImplicit false
 theorem reconstruct_channels (xs : Array (Array U64 3#usize) 3#usize) :
    ∃ z, host_arithmetic.reconstruct_channels xs = ok z ∧ Q z := by
  obtain ⟨a,ha⟩ := index_total xs 0#usize (by decide)
  obtain ⟨b,hb⟩ := index_total xs 1#usize (by decide)
  obtain ⟨c,hc⟩ := index_total xs 2#usize (by decide)
  obtain ⟨m0,h0,c0⟩ := reconstruct_component a
  obtain ⟨m1,h1,c1⟩ := reconstruct_component b
  obtain ⟨m2,h2,c2⟩ := reconstruct_component c
  obtain ⟨r,hr,cr⟩ := host_mulr m1 c1
  obtain ⟨d,hd,cd⟩ := current_cadd m0 r c0 cr
  obtain ⟨e,he,ce⟩ := current_csub m2 m0 c2 c0
  obtain ⟨f,hf,cf⟩ := current_csub e m1 ce c1
  refine ⟨⟨d,f⟩,?_,cd,cf⟩
  simp only [host_arithmetic.reconstruct_channels,ha,hb,hc,h0,h1,h2,hr,hd,he,hf,bind_tc_ok]
#print axioms reconstruct_channels
end PV_B3_Canonical
