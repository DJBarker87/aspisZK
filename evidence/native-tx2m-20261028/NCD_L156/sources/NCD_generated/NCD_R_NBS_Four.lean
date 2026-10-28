-- Retargeted inherited proof body; only module imports changed.
import NCD_R_NBS_DotWhole
import NCD_R_NBS_PowersCanon
set_option autoImplicit false
noncomputable section
namespace NBS_Four
open Aeneas Aeneas.Std Result AspisR1

def prefix608 (q : Slice U8) (bound : 608≤q.val.length) : Array U8 608#usize :=
  ⟨q.val.take 608,by change (q.val.take 608).length=608; simp only [List.length_take];omega⟩

/-- The exact prefix608 conversion is derived from source range geometry. -/
theorem prefix_read (q : Slice U8) (bound : 608≤q.val.length) :
    (do let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
          q {«end»:=608#usize}
        let r ← core.array.TryFromSharedArraySlice.try_from 608#usize s
        core.result.Result.unwrap core.fmt.DebugTryFromSliceError r)=ok (prefix608 q bound) := by
  let selected : Slice U8 := ⟨q.val.take 608,by have:=q.property; simp only [List.length_take];omega⟩
  have range := JFo_PrefixRead.source q 608#usize bound selected rfl
  rw [range,bind_tc_ok]
  have len : selected.len=608#usize := by
    apply UScalar.eq_of_val_eq
    change (q.val.take 608).length=608
    simp only [List.length_take];omega
  simp only [core.array.TryFromSharedArraySlice.try_from,len,if_pos rfl,bind_tc_ok,
    core.result.Result.unwrap]
  rfl

def slots (q : Array U8 608#usize) (g : Array FIo_Install.NE 29#usize) :
    Result (Array FIo_Install.NE 4#usize) := do
  let a ← FIp_NativeDots.fast_dots.four_dots_one q g 0#usize
  let b ← FIp_NativeDots.fast_dots.four_dots_one q g 1#usize
  let c ← FIp_NativeDots.fast_dots.four_dots_one q g 2#usize
  let d ← FIp_NativeDots.fast_dots.four_dots_one q g 3#usize
  ok (Array.make 4#usize [a,b,c,d])

/-- All four calls compose on the SAME derived prefix608 and coefficient array.
Domains are scalar/tail byte-decoder domains; no dot result is assumed. -/
theorem source (q : Slice U8) (bound : 608≤q.val.length)
    (g : Array FIo_Install.NE 29#usize) (hg : FIo_ArrayCanon.Holds g)
    (decoded : ∀ slot : Fin 4, NBS_DotTerm.Scalars (prefix608 q bound)
      (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac)))
    (tails : ∀ slot : Fin 4, NBS_DotTail.Domain (prefix608 q bound) slot) :
    ∃ out, FIp_NativeDots.fast_dots.four_dots q g=ok out ∧ FIo_ArrayCanon.Holds out := by
  obtain ⟨a,h0,c0⟩ := NBS_DotWhole.source (prefix608 q bound) 0 g hg (decoded 0) (tails 0)
  obtain ⟨b,h1,c1⟩ := NBS_DotWhole.source (prefix608 q bound) 1 g hg (decoded 1) (tails 1)
  obtain ⟨c,h2,c2⟩ := NBS_DotWhole.source (prefix608 q bound) 2 g hg (decoded 2) (tails 2)
  obtain ⟨d,h3,c3⟩ := NBS_DotWhole.source (prefix608 q bound) 3 g hg (decoded 3) (tails 3)
  have z0 : Usize.ofNat ((0:Fin 4).val) (by have:=(0:Fin 4).isLt;scalar_tac)=0#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [z0] at h0
  have z1 : Usize.ofNat ((1:Fin 4).val) (by have:=(1:Fin 4).isLt;scalar_tac)=1#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [z1] at h1
  have z2 : Usize.ofNat ((2:Fin 4).val) (by have:=(2:Fin 4).isLt;scalar_tac)=2#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [z2] at h2
  have z3 : Usize.ofNat ((3:Fin 4).val) (by have:=(3:Fin 4).isLt;scalar_tac)=3#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [z3] at h3
  have joined := congrArg (fun selected : Result (Array U8 608#usize) => do
    let p ← selected
    slots p g) (prefix_read q bound)
  have routed : FIp_NativeDots.fast_dots.four_dots q g=slots (prefix608 q bound) g := by
    simpa only [FIp_NativeDots.fast_dots.four_dots,slots,bind_assoc_eq,bind_tc_ok] using joined
  let out : Array FIo_Install.NE 4#usize := Array.make 4#usize [a,b,c,d]
  refine ⟨out,?_,?_⟩
  · rw [routed]
    simp only [slots,h0,h1,h2,h3,bind_tc_ok]
    rfl
  · intro x hx
    change x∈[a,b,c,d] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption

#print axioms prefix_read
#print axioms source
end NBS_Four
