import TxS_RawFinish
set_option autoImplicit false
noncomputable section
namespace AspisR1.TxS_LegacyFinish
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem forget {W : Type} (finish : FinishOps W)
    (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
    (proof : Slice U8) (saved : alloc.vec.Vec U8) (H : Bytes → State)
    (stored pub : Bytes) (tx1p : AspisR1CurrentCaller.verifier.Prepared) (parsed : OraclePortCompactDraft.Parsed)
    (trace : List (Bytes × State))
    (new : TxS_RawFinish.Outcome finish v p a proof saved H stored pub tx1p parsed trace) :
    T2R_Finish.Outcome finish v p a proof saved H stored pub tx1p parsed trace := by
  obtain ⟨s2,alpha0,alpha1,alphas,ha0,ha1,has,typed⟩ :=
    TxS_RawFinish.to_typed finish v p a proof saved H stored pub tx1p parsed trace new
  refine ⟨s2,alpha0,alpha1,alphas,ha0,ha1,has,?_⟩
  intro r0 r1 weights pair dot hw hp hd semantic q tr i hi hq read decoded pairing matchesLaw equation dotLaw canonical c prepare savedEq
  exact typed r0 r1 weights pair dot hw hp hd semantic q tr i hi hq read decoded pairing matchesLaw equation dotLaw canonical prepare

#print axioms forget
end AspisR1.TxS_LegacyFinish
end
