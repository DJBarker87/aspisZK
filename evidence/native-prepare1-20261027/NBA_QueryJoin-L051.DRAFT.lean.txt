import NBA_QueryFactor
namespace AspisR1.NBA_QueryJoin
open AspisR1.NBA_QueryFactor
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
theorem source (B : QueriesModel.Boundaries) {H : Type}
    (D : aspis_core.Digest32 H) (self : transcript.Transcript H) (row : U8) (payload : Slice U8) :
    QueriesModel.queries B D self row payload=queriesFactored B D self row payload := by
  unfold QueriesModel.queries queriesFactored materialize
  simp only [lift,bind_tc_ok]
  have firstIndex : Array.index_mut_usize (Array.repeat 8#usize (Array.repeat 32#usize 0#u8)) 0#usize =
      ok (Array.repeat 32#usize 0#u8,fun x => (Array.repeat 8#usize (Array.repeat 32#usize 0#u8)).set 0#usize x) := by rfl
  rw [firstIndex]
  simp only [bind_tc_ok]
  dsimp! only
  simp only [bind_assoc_eq,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.NBA_QueryJoin
