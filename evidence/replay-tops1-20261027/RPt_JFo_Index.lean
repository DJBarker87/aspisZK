import RPt_JFq_Range
set_option autoImplicit false
namespace AspisR1.JFo_Index
open Aeneas Aeneas.Std Result WP

theorem source (bytes : Slice U8) (i : Usize) (bound : i.val<bytes.length)
    (byte : U8) (selected : bytes.val[i.val]?=some byte) :
    Slice.index_usize bytes i=ok byte := by
  have spec : Slice.index_usize bytes i ⦃ out => out=byte ⦄ := by
    step*
    trace_state
    simp_all
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms source
end AspisR1.JFo_Index
