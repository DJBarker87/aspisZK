import T2R_Finish
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2R_Legacy
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical OraclePortCompactDraft

theorem finish {W : Type} (ops : FinishOps W) (v : verifier.View)
    (p : verifier.Prepared) (a : verifier.Accumulator) (proof : Slice U8)
    (saved : alloc.vec.Vec U8) (H : Bytes → State) (stored publicBytes : Bytes)
    (tx1p : AspisR1CurrentCaller.verifier.Prepared) (parsed : Parsed)
    (trace : List (Bytes × State))
    (new : T2R_Finish.Outcome ops v p a proof saved H stored publicBytes tx1p parsed trace) :
    Cons_Finish.Outcome ops v p a proof saved H stored publicBytes tx1p parsed trace := by
  obtain ⟨variant,x0,x1,xs,h0,h1,hs,body⟩ := new
  intro alpha0 alpha1 r0 r1 weights alphas pair dot s2 ha0 ha1 hw has hp hd
  have e0 : x0 = alpha0 := Result.ok.inj (h0.symm.trans ha0)
  have e1 : x1 = alpha1 := Result.ok.inj (h1.symm.trans ha1)
  have es : xs = alphas := Result.ok.inj (hs.symm.trans has)
  subst alpha0
  subst alpha1
  subst alphas
  exact body r0 r1 weights pair dot hw hp hd

#print axioms finish
end AspisR1.T2R_Legacy
end
