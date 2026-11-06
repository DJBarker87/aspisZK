import NJQ_Read
set_option autoImplicit false
namespace NJQ_MasterBinding
open Aeneas Aeneas.Std Result WP
open NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts

def binding : Array U8 32#usize := Array.make 32#usize
 [65#u8,83#u8,80#u8,73#u8,83#u8,70#u8,79#u8,82#u8,69#u8,83#u8,84#u8,56#u8,
  2#u8,2#u8,2#u8,8#u8,1#u8,20#u8,1#u8,
  0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]

/-- The actual frozen format constant, including version/count casts; no free slot. -/
theorem source : POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING=ok binding := by
 have spec : POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING ⦃ out=>out=binding ⦄ := by
  unfold POOL_V1_PAIR_FOREST_ACCOUNT_FORMAT_BINDING POOL_V1_PAIR_FOREST_MASTER_VERSION
   POOL_V1_PAIR_FOREST_LANE_VERSION POOL_V1_PAIR_FOREST_CHECKPOINT_VERSION
   POOL_V1_PAIR_FOREST_LANE_COUNT
   NJI_Extracted.aspis_statement.pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
   NJI_Extracted.aspis_statement.pool_v1.format.POOL_V1_TREE_DEPTH
  step*
  all_goals simp_all [binding]
  all_goals have h8 : UScalar.cast .U8 8#usize=8#u8 := by scalar_tac
  all_goals have h20 : UScalar.cast .U8 20#usize=20#u8 := by scalar_tac
  all_goals simp only [h8,h20]
 obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
 rw [same] at call
 exact call

#print axioms source
end NJQ_MasterBinding
