/- Generated R120 fixed-weight certificate. No query recurrence is evaluated. -/
import AspisV8R19.TwoSwapChannel0
import AspisV8R19.TwoSwapChannel1
import AspisV8R19.TwoSwapCodeChunk00
import AspisV8R19.TwoSwapCodeChunk01
import AspisV8R19.TwoSwapCodeChunk02
import AspisV8R19.TwoSwapCodeChunk03
import AspisV8R19.TwoSwapCodeChunk04
import AspisV8R19.TwoSwapCodeChunk05
import AspisV8R19.TwoSwapCodeChunk06
import AspisV8R19.TwoSwapCodeChunk07
import AspisV8R19.TwoSwapCodeChunk08
import AspisV8R19.TwoSwapWeightsChunk00
import AspisV8R19.TwoSwapWeightsChunk01
import AspisV8R19.TwoSwapWeightsChunk02
import AspisV8R19.TwoSwapWeightsChunk03
import AspisV8R19.TwoSwapWeightsChunk04
import AspisV8R19.TwoSwapWeightsChunk05
import AspisV8R19.TwoSwapWeightsChunk06
import AspisV8R19.TwoSwapWeightsChunk07
namespace AspisR19.TwoSwapWitness
open RootCertificate HighRepairInvariant ResidualModel AspisV8R17
noncomputable section
theorem code_correct (which : Fin 3) (j : Fin 131) : codeFormula which.val j.val=codeValues which.val j.val := by
  by_cases h0 : j.val<16
  · have h := code_chunk0 which ⟨j.val-0,by omega⟩
    simpa only [Nat.sub_add_cancel (show 0≤j.val by omega)] using h
  by_cases h1 : j.val<32
  · have h := code_chunk1 which ⟨j.val-16,by omega⟩
    simpa only [Nat.sub_add_cancel (show 16≤j.val by omega)] using h
  by_cases h2 : j.val<48
  · have h := code_chunk2 which ⟨j.val-32,by omega⟩
    simpa only [Nat.sub_add_cancel (show 32≤j.val by omega)] using h
  by_cases h3 : j.val<64
  · have h := code_chunk3 which ⟨j.val-48,by omega⟩
    simpa only [Nat.sub_add_cancel (show 48≤j.val by omega)] using h
  by_cases h4 : j.val<80
  · have h := code_chunk4 which ⟨j.val-64,by omega⟩
    simpa only [Nat.sub_add_cancel (show 64≤j.val by omega)] using h
  by_cases h5 : j.val<96
  · have h := code_chunk5 which ⟨j.val-80,by omega⟩
    simpa only [Nat.sub_add_cancel (show 80≤j.val by omega)] using h
  by_cases h6 : j.val<112
  · have h := code_chunk6 which ⟨j.val-96,by omega⟩
    simpa only [Nat.sub_add_cancel (show 96≤j.val by omega)] using h
  by_cases h7 : j.val<128
  · have h := code_chunk7 which ⟨j.val-112,by omega⟩
    simpa only [Nat.sub_add_cancel (show 112≤j.val by omega)] using h
  have h := code_chunk8 which ⟨j.val-128,by omega⟩
  simpa only [Nat.sub_add_cancel (show 128≤j.val by omega)] using h
#print axioms code_correct
theorem weights_correct (which : Fin 3) (j : Fin 128) : pointFormula which.val j.val=pointValues which.val j.val := by
  by_cases h0 : j.val<16
  · have h := weights_chunk0 which ⟨j.val-0,by omega⟩
    simpa only [Nat.sub_add_cancel (show 0≤j.val by omega)] using h
  by_cases h1 : j.val<32
  · have h := weights_chunk1 which ⟨j.val-16,by omega⟩
    simpa only [Nat.sub_add_cancel (show 16≤j.val by omega)] using h
  by_cases h2 : j.val<48
  · have h := weights_chunk2 which ⟨j.val-32,by omega⟩
    simpa only [Nat.sub_add_cancel (show 32≤j.val by omega)] using h
  by_cases h3 : j.val<64
  · have h := weights_chunk3 which ⟨j.val-48,by omega⟩
    simpa only [Nat.sub_add_cancel (show 48≤j.val by omega)] using h
  by_cases h4 : j.val<80
  · have h := weights_chunk4 which ⟨j.val-64,by omega⟩
    simpa only [Nat.sub_add_cancel (show 64≤j.val by omega)] using h
  by_cases h5 : j.val<96
  · have h := weights_chunk5 which ⟨j.val-80,by omega⟩
    simpa only [Nat.sub_add_cancel (show 80≤j.val by omega)] using h
  by_cases h6 : j.val<112
  · have h := weights_chunk6 which ⟨j.val-96,by omega⟩
    simpa only [Nat.sub_add_cancel (show 96≤j.val by omega)] using h
  have h := weights_chunk7 which ⟨j.val-112,by omega⟩
  simpa only [Nat.sub_add_cancel (show 112≤j.val by omega)] using h
#print axioms weights_correct
end
end AspisR19.TwoSwapWitness
