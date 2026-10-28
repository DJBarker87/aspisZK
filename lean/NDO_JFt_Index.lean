import NDO_JFt_LocalWindow
set_option autoImplicit false
namespace AspisR1.JFt_Index
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

/-- Reads one of the small checked metadata windows, without reducing public1880. -/
theorem window (off n index : Nat) (bound : off+n≤1880) (inside : index<n)
    (i : Usize) (same : i.val=index) (byte : U8) (xs : List U8)
    (selected : (JFx_NativeBytes.publicInput.val.drop off).take n=xs)
    (value : xs[index]?=some byte) :
    Slice.index_usize (JFu_PublicRange.segment off n bound) i=ok byte := by
  apply source _ i (by rw [JFu_PublicRange.length,same];exact inside) byte
  change ((JFx_NativeBytes.publicInput.val.drop off).take n)[i.val]?=some byte
  rw [selected,same]
  exact value

#print axioms source
#print axioms window
end AspisR1.JFt_Index
