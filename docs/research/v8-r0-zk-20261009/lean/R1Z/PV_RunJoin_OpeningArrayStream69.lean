import R1Z.PV_RunJoin_OpeningStreamUnique69
import R1Z.PV_RunJoin_PublishSkeleton54
import R1Z.PV_RunJoin_WideImage43
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OpeningArrayStream69
open Aeneas Aeneas.Std ProverCommitWideOps48 ProverCommitMix48
attribute [local irreducible] source List.ofFn

theorem complete (n : Usize) (x y : Nat → Raw)
    (hx : ∀ i,i<n.val → canonical (x i)) (hy : ∀ i,i<n.val → canonical (y i))
    (h : sourceArray n x=sourceArray n y) :
    ProverCommitOpeningBytes49.stream n.val x hx=ProverCommitOpeningBytes49.stream n.val y hy := by
  exact PV_RunJoin_OpeningStreamUnique69.stream n.val x y hx hy (congrArg Subtype.val h)

theorem byte : PV_RunJoin_WideImage43.byte=(fun x : U8 => UInt8.ofNat x.val) := by
  funext x
  apply UInt8.toNat_inj.mp
  simp [PV_RunJoin_WideImage43.byte,PV_RunJoin_WidePoint43.byte,
    ProverCommitWordBytes47.rawByte,UScalar.val]

#print axioms complete
#print axioms byte
end R1Z.PV_RunJoin_OpeningArrayStream69
