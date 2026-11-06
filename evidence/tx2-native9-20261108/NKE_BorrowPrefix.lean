import NKE_GeometryCuts
import NKE_CommonDomain
import NJJ_Constructors
set_option autoImplicit false
noncomputable section
namespace NKE_BorrowPrefix
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages NJU_CommonObserved
abbrev E := aspis_core.field.wide_exact.WideExact
/-- Only Prepared and powers payloads in the borrowed expression prefix.
Proof handle/size observations do NOT supply a proof-byte equality here. -/
structure Cut (p nativeP : verifier.Prepared) (g nativeG : Array E 29#usize) : Prop where
 prepared : NJJ_Constructors.PreparedCut p nativeP
 powers : ∀ i : Fin 29,nativeG.val[i.val]?=g.val[i.val]?

theorem same (p nativeP : verifier.Prepared) (g nativeG : Array E 29#usize)
 (cut : Cut p nativeP g nativeG) : nativeP=p ∧ nativeG=g :=
 ⟨NJJ_Constructors.prepared p nativeP cut.prepared,
  NJJ_Constructors.array_ext nativeG g cut.powers⟩

/-- Instantiate this partial native prefix at the actual C07 occurrence.
Owned a/pending transfer, geometry, proof payload, reply and drop prefixes are
NOT replaced or discharged. This theorem is not a positive parent root. -/
theorem at_actual (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (p nativeP : verifier.Prepared) (a : verifier.Accumulator)
 (g nativeG : Array E 29#usize) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) (reply : R (verifier.Accumulator × verifier.BatchedWeights))
 (_entered : Event.query proof p a g geometry pending reply∈
  (run wr rr merkle finish d pub proof ck hash none).events)
 (cut : Cut p nativeP g nativeG) :
 NJJ_Common.query proof nativeP a nativeG none geometry pending 22#usize=
 NJJ_Common.query proof p a g none geometry pending 22#usize := by
 obtain ⟨hp,hg⟩ := same p nativeP g nativeG cut
 rw [hp,hg]
/-- The separate geometry borrowed-prefix window substitutes that SAME geometry
without changing any other argument. Caller12/12 is derived at C05; attaching
that domain across the C07 ownership step remains separate. -/
theorem geometry (p : verifier.Prepared) (a : verifier.Accumulator)
 (proof : Slice U8) (g : Array E 29#usize)
 (before after : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
 (inverseSize : before.inverses.val.length=12) (lineSize : before.line_z.val.length=12)
 (cut : NKE_GeometryCuts.Cut before after) :
 NJJ_Common.query proof p a g none after pending 22#usize=
 NJJ_Common.query proof p a g none before pending 22#usize := by
 rw [NKE_GeometryCuts.same before after inverseSize lineSize cut]
#print axioms geometry
#print axioms same
#print axioms at_actual
end NKE_BorrowPrefix
