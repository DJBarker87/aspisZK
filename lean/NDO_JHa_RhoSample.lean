import NDO_JHa_CurrentFields
import NDO_JGg_Opening32
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_RhoSample
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge

def value : aspis_core.field.QM31 :=
  ⟨⟨1497225503#u32,277942247#u32⟩,⟨877802089#u32,1707877402#u32⟩⟩

theorem computed : AspisR1.SamplerNatModel.qm31Digits
    (AspisR1.SourceSamplerByteRank.rank (encodeState JGg_Opening32.block0))=
      [1497225503,277942247,877802089,1707877402] := by
  rw [←AspisR1.SourceSamplerByteRank.word_value]
  with_unfolding_all rfl
#print axioms computed

theorem sample : AspisR1PublicPreparation.sampler.qm31_sample (encodeState JGg_Opening32.block0)=ok value := by
  obtain ⟨q,call,_,coords⟩ := SamplerTransport.sample_total (encodeState JGg_Opening32.block0)
  rw [computed] at coords
  have parts := List.cons.inj coords
  have p0 : q.c0.a=1497225503#u32 := UScalar.eq_of_val_eq parts.1
  have parts := List.cons.inj parts.2
  have p1 : q.c0.b=277942247#u32 := UScalar.eq_of_val_eq parts.1
  have parts := List.cons.inj parts.2
  have p2 : q.c1.a=877802089#u32 := UScalar.eq_of_val_eq parts.1
  have parts := List.cons.inj parts.2
  have p3 : q.c1.b=1707877402#u32 := UScalar.eq_of_val_eq parts.1
  have same : q=value := by
    rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩
    simp only at p0 p1 p2 p3
    cases p0
    cases p1
    cases p2
    cases p3
    rfl
  exact same ▸ call
#print axioms sample
end AspisR1.JHa_RhoSample
end
