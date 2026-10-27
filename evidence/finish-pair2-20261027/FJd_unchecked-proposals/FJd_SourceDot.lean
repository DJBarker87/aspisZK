import FIo_MixedValues
import FJd_ReferenceDot
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJd_SourceDot
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE NQ wide qm)
/-- Safe left-fold reference for EbyKDot, in push order. -/
def reference : List (NE × NQ) → NE → Result NE
  | [],acc=>ok acc
  | (a,b)::xs,acc=>do
    let product ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 a b
    let next ← FIo_Native.aspis_core.field.wide_exact.WideExact.add acc product
    reference xs next

def product (a : NE × NQ) : OraclePortCheckpointAbiC5.E :=
  decodeWide (wide a.1)*algebraMap OraclePortCheckpointAbiC5.K
    OraclePortCheckpointAbiC5.E (decodeQM (qm a.2))

theorem value (xs : List (NE × NQ)) (before after : NE)
    (hx : ∀ x∈xs,FIo_WideValues.Canon x.1)
    (hb : FIo_WideValues.Canon before)
    (run : reference xs before=ok after) :
    FIo_WideValues.Canon after ∧
      decodeWide (wide after)=decodeWide (wide before)+(xs.map product).sum := by
  induction xs generalizing before with
  | nil => cases Result.ok.inj run;exact ⟨hb,by simp⟩
  | cons x xs ih =>
    simp only [reference] at run
    obtain ⟨p,hp,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨next,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    have hxc : FIo_WideValues.Canon x.1 := hx x (List.mem_cons_self ..)
    have vp := FIo_MixedValues.mul_qm x.1 p x.2 hxc hp
    have vn := FIo_WideValues.add before p next hb vp.1 hn
    have htail : ∀ x∈xs,FIo_WideValues.Canon x.1 := by
      intro y hy;exact hx y (List.mem_cons_of_mem _ hy)
    obtain ⟨canon,hvalue⟩ := ih htail _ vn.1 run
    refine ⟨canon,?_⟩
    rw [hvalue,vn.2,vp.2]
    simp only [List.map_cons,List.sum_cons,product]
    exact add_assoc _ _ _
#print axioms value
end AspisR1.FJd_SourceDot
end
