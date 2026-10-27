import RPt_JFs_TX2_Raw
set_option autoImplicit false
namespace AspisR1.FJf_RawReference
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMath (extend)
open JFs_TX2_RawMap (pack)
abbrev add := U64.wrapping_add
abbrev sub := U64.wrapping_sub
abbrev mul := U64.wrapping_mul

def product (a b : U32) : U64 := mul (extend a) (extend b)
def u (c d g h : U32) : U64 :=
  FIo_ReduceBounds.fold (sub (add (product c g) 4611686014132420609#u64) (product d h))
def v (c d g h : U32) : U64 := FIo_ReduceBounds.fold (add (product c h) (product d g))
def raw0 (a b c d e f g h : U32) : U64 :=
  sub (add (add (sub (add (product a e) 4611686014132420609#u64) (product b f))
    (mul 2#u64 (u c d g h))) 6442450941#u64) (v c d g h)
def raw1 (a b c d e f g h : U32) : U64 :=
  add (add (add (product a f) (product b e)) (u c d g h)) (mul 2#u64 (v c d g h))
def raw2 (a b c d e f g h : U32) : U64 :=
  sub (sub (add (add (product a g) (product c e)) 9223372028264841218#u64) (product b h)) (product d f)
def raw3 (a b c d e f g h : U32) : U64 :=
  add (add (add (product a h) (product b g)) (product c f)) (product d e)

theorem source (a b c d e f g h : U32) :
    FIo_Native.fast_pairing.canonical.Q.raw (pack a b c d) (pack e f g h)=
      ok (pack (raw0 a b c d e f g h) (raw1 a b c d e f g h)
        (raw2 a b c d e f g h) (raw3 a b c d e f g h)) := by
  have r0 : Array.index_usize (pack (extend a) (extend b) (extend c) (extend d)) 0#usize=ok (extend a) := rfl
  have r1 : Array.index_usize (pack (extend a) (extend b) (extend c) (extend d)) 1#usize=ok (extend b) := rfl
  have r2 : Array.index_usize (pack (extend a) (extend b) (extend c) (extend d)) 2#usize=ok (extend c) := rfl
  have r3 : Array.index_usize (pack (extend a) (extend b) (extend c) (extend d)) 3#usize=ok (extend d) := rfl
  have r4 : Array.index_usize (pack (extend e) (extend f) (extend g) (extend h)) 0#usize=ok (extend e) := rfl
  have r5 : Array.index_usize (pack (extend e) (extend f) (extend g) (extend h)) 1#usize=ok (extend f) := rfl
  have r6 : Array.index_usize (pack (extend e) (extend f) (extend g) (extend h)) 2#usize=ok (extend g) := rfl
  have r7 : Array.index_usize (pack (extend e) (extend f) (extend g) (extend h)) 3#usize=ok (extend h) := rfl
  unfold FIo_Native.fast_pairing.canonical.Q.raw FIo_QRaw.canonical.Q.raw
  simp only [JFs_TX2_RawMap.left,JFs_TX2_RawMap.right,bind_tc_ok,r0,r1,r2,r3,r4,r5,r6,r7,
    JFs_TX2_RawMath.mul,JFs_TX2_RawMath.pp,JFs_TX2_RawMath.fold,JFs_TX2_RawMath.twice_fold,
    JFs_TX2_RawMath.twice_pp,JFs_TX2_RawMath.triple_p,lift]
  rfl
#print axioms source
end AspisR1.FJf_RawReference
