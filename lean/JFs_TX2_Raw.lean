import JFs_TX2_RawMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_Raw
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
open JFs_TX2_RawMath
theorem packed (a b c d e f g h : U32) :
    ∃ out, FIo_Native.fast_pairing.canonical.Q.raw (pack a b c d) (pack e f g h)=ok out := by
  have r0 : Array.index_usize (pack (extend a) (extend b) (extend c) (extend d)) 0#usize=ok (extend a) := rfl
  have r1 : Array.index_usize (pack (extend a) (extend b) (extend c) (extend d)) 1#usize=ok (extend b) := rfl
  have r2 : Array.index_usize (pack (extend a) (extend b) (extend c) (extend d)) 2#usize=ok (extend c) := rfl
  have r3 : Array.index_usize (pack (extend a) (extend b) (extend c) (extend d)) 3#usize=ok (extend d) := rfl
  have r4 : Array.index_usize (pack (extend e) (extend f) (extend g) (extend h)) 0#usize=ok (extend e) := rfl
  have r5 : Array.index_usize (pack (extend e) (extend f) (extend g) (extend h)) 1#usize=ok (extend f) := rfl
  have r6 : Array.index_usize (pack (extend e) (extend f) (extend g) (extend h)) 2#usize=ok (extend g) := rfl
  have r7 : Array.index_usize (pack (extend e) (extend f) (extend g) (extend h)) 3#usize=ok (extend h) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [left,right,bind_tc_ok,r0,r1,r2,r3,r4,r5,r6,r7,JFs_TX2_RawMath.mul,
    pp,fold,twice_fold,twice_pp,triple_p,lift]
  exact ⟨_,rfl⟩

theorem source (a b : FIo_Native.fast_pairing.canonical.Q) :
    ∃ out, FIo_Native.fast_pairing.canonical.Q.raw a b=ok out := by
  obtain ⟨a0,a1,a2,a3,rfl⟩ := shape a
  obtain ⟨b0,b1,b2,b3,rfl⟩ := shape b
  exact packed a0 a1 a2 a3 b0 b1 b2 b3

#print axioms packed
#print axioms source
end AspisR1.JFs_TX2_Raw
end
