import Hiq_DecodedShape
import Hist_ArgumentCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_FirstShape
open Aeneas Aeneas.Std Result DrvC_Installation

theorem decoded {F C : Type} (c : Configuration F C)
    (semantic : AdapterRw.LeadInputs.Public) (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (first : AdapterRw.first_decoded (sdk c) semantic pub proof split = ok (.Ok saved)) :
    Hist_Store.Initialized saved.deref ∧ saved.val.length = 1768 := by
  rw [cphy_dictionary,Uni_Install.compose_tx1] at first
  exact Hiq_DecodedShape.shape _ (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std
    semantic pub proof split saved first

theorem source {F C : Type} (c : Configuration F C) (id : S2W_ExtractionBoundary.Program)
    (accounts : S2W_ExtractionBoundary.Accounts) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned (sdk c) id accounts data = ok (.Ok saved)) :
    Hist_Store.Initialized saved.deref ∧ saved.val.length = 1768 := by
  obtain ⟨pa,pu,pub,raw,stmt,semantic,proof,split,_,_,_,_,_,_,_,first,_⟩ :=
    AdapterRw.Accepted.first_call (sdk c) id accounts data saved accepted
  exact decoded c semantic pub proof split saved first

#print axioms decoded
#print axioms source
end AspisR1.Hiq_FirstShape
end
