import RPz7_S1QueryMaterializeProgramV1
import RPz7_S1QueryByteChainV1
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.PreparedQueryMaterialize
open Aeneas Aeneas.Std Result
open FS FS2 FS2.Duplex
open PreparedHashCode PreparedHashCode.QueryPair
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps

/-- Length-checked carrier adapter. The n=8 chain below always reaches the
first branch, proved by complete program equality; no default digest is used. -/
def packEight : List State → List State → Result (Blocks8 × Blocks8)
  | [b0,b1,b2,b3,b4,b5,b6,b7],[x0,x1,x2,x3,x4,x5,x6,x7] =>
    ok (Array.make 8#usize [encodeState b0,encodeState b1,encodeState b2,encodeState b3,
      encodeState b4,encodeState b5,encodeState b6,encodeState b7],
      Array.make 8#usize [encodeState x0,encodeState x1,encodeState x2,encodeState x3,
      encodeState x4,encodeState x5,encodeState x6,encodeState x7])
  | _,_ => .fail .panic

def modelMaterialize {M Cv : Type} {L : Nat} (p : Params M Cv L) (state : Bytes32) :
    Program Bytes State (Result (Blocks8 × Blocks8)) :=
  rename Addr.toBytes (AspisR1.QuerySampler.chain p packEight 8 (decodeState state) [] []).toProgram

/-- Exact fixed mathematical sampler program, including full source arrays,
all sixteen ordered asks and returned Result. No success or range premise. -/
theorem materialize_eq_model {H M Cv : Type} {L : Nat} (p : Params M Cv L)
    (D : aspis_core.Digest32 H) (hash : H) (state : Bytes32) :
    oracleProgram (materialize effects D hash state)=modelMaterialize p state := by
  rw [materialize_program]
  unfold modelMaterialize
  rw [← pairedBytesProgram_eq_model p packEight 8 (decodeState state) [] []]
  simp only [normalMaterialize,pairedBytesProgram,packEight,List.nil_append,
    List.cons_append,List.append_nil,array_roundtrip]

#print axioms materialize_eq_model
end AspisR1PublicPreparation.PreparedQueryMaterialize
