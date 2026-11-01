import R1Z.PV_RDCD4_EncoderRefinement
import R1Z.PV_DL_EncoderNative
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDCD4_EncoderEntries
set_option autoImplicit false

/-- The source's two checked reads, followed by the original four field calls.
The short-slice panic arm is retained, then excluded by the chunk shape law. -/
def fieldStep {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (entry : List E × E) (acc : E × E) : Result (E × E) :=
  match entry.1 with
  | a::b::_ => PV_DL_EncoderZip.applyEntry inst ((a,b),entry.2) acc.1 acc.2
  | _ => fail .panic

theorem run_bridge {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (xs ys : List E) (p0 p1 : E) :
    PV_RDCD4_EncoderLoop.run (fieldStep inst)
      ((PV_RDCD4_EncoderLoop.pairs xs).zip ys) (p0,p1) =
    PV_DL_EncoderNative.run inst ((PV_DL_EncoderPairs.chunks xs).zip ys) p0 p1 := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => rfl
    | cons b tail =>
      cases ys with
      | nil => rfl
      | cons n rest =>
        change (do
          let acc ← PV_DL_EncoderZip.applyEntry inst ((a,b),n) p0 p1
          PV_RDCD4_EncoderLoop.run (fieldStep inst)
            ((PV_RDCD4_EncoderLoop.pairs tail).zip rest) acc) =
          (do
          let acc ← PV_DL_EncoderZip.applyEntry inst ((a,b),n) p0 p1
          PV_DL_EncoderNative.run inst ((PV_DL_EncoderPairs.chunks tail).zip rest) acc.1 acc.2)
        apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
        intro acc _
        rcases acc with ⟨u,v⟩
        exact run_bridge inst tail rest u v
termination_by xs.length

/-- Exactly 512 source iterations and one exhausted inspection. -/
theorem iteration {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (b : Array E 512#usize) (p0 p1 : E) :
    PV_RDCD4_EncoderLoop.loop (fieldStep inst) 513
      (PV_RDCD4_Zip194.new (PV_RDCD4_Chunks194.new q.val)
        (PV_RDCD4_ArrayIter194.new b.val)) (p0,p1) =
      PV_DL_EncoderNative.run inst (PV_DL_EncoderZip.entries q b) p0 p1 := by
  have hq : q.val.length=1024 := q.property
  have hb : b.val.length=512 := b.property
  rw [PV_RDCD4_Chunks194.message_new q.val hq]
  have h := PV_RDCD4_EncoderRefinement.source (fieldStep inst) 512 q.val
    (PV_RDCD4_ArrayIter194.new b.val) 0 0 (p0,p1)
    (by omega) (by change 0+512=b.val.length; omega) rfl
  change PV_RDCD4_EncoderLoop.loop (fieldStep inst) (512+1)
    (⟨⟨q.val,[]⟩,PV_RDCD4_ArrayIter194.new b.val,0,0⟩ : PV_RDCD4_EncoderLoop.Iter E) _ = _
  rw [h,PV_RDCD4_ArraySuffix.new_remaining,run_bridge]
  rfl

#print axioms run_bridge
#print axioms iteration
end R1Z.PV_RDCD4_EncoderEntries
