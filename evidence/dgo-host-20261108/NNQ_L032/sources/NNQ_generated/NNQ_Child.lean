import NNQ_FirstCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result

theorem child_sim {F C A : Type} (c : DrvC_Installation.Configuration F C)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize))
    (hv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (x y : S2W_Trace.Call A) (h : CallSim x y) :
    GExq_ChildCode.execute (withDigest c o).adapter (withDigest c o).currentBase
      (AuS1_Install.base (withDigest c o).stageBase) (withDigest c o).finish
      (withDigest c o).reserved (withDigest c o).query (withDigest c o).geometry
      (withDigest c o).boundaries (withDigest c o).std hv x =
    GExq_ChildCode.execute c.adapter c.currentBase (AuS1_Install.base c.stageBase)
      c.finish c.reserved c.query c.geometry c.boundaries c.std hv y := by
  cases h with
  | same x hn =>
    cases x <;> try rfl
    exact False.elim (hn rfl)
  | op10 D1 D2 hc semantic pub proof split hash obs =>
    simp only [GExq_ChildCode.execute, withDigest]
    rw [firstCode_eq _ _ _ _ (AspisS6CurrentFirstInstallation.toDigest D1)
      (AspisS6CurrentFirstInstallation.toDigest D2)]
  | op11 D1 D2 hc pub proof ck hash obs =>
    simp only [GExq_ChildCode.execute, withDigest]
    exact secondCode_eq _ _ _ D1 D2 _ _ _ _
#print axioms child_sim
end AspisR1.NNQ_HostDigest
end
