import NLK_LaneLoop
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NLK_LaneTrace
open Aeneas Aeneas.Std Result NKP_LaneCuts
abbrev Sized := NLK_LaneInput.Sized
/-- Rule-B aggregation of the native per-occurrence cuts. Every node keeps
its SAME original input bytes, actual level, before/after frontier and exact
reply. No arbitrary step function or whole-loop equality is a field. -/
inductive Cut (p : Sized) (next : U64) :
 List (Fin 20) → Frontier → Reply × Frontier × List (Fin 20) → Prop
 | empty (before : Frontier) : Cut p next [] before (.Ok (),before,[])
 | rejected (level : Fin 20) (rest : List (Fin 20)) (before after : Frontier) (e : NKF_BoxModel.PE)
   (one : IterationCut (NLK_LaneTable.empty level) (NLK_LaneLoop.occupied next level)
    before after level (NLK_LaneLoop.raw p level) (.Err e)) :
   Cut p next (level::rest) before (.Err e,after,[level])
 | continued (level : Fin 20) (rest : List (Fin 20)) (before after final : Frontier)
   (reply : Reply) (calls : List (Fin 20))
   (one : IterationCut (NLK_LaneTable.empty level) (NLK_LaneLoop.occupied next level)
    before after level (NLK_LaneLoop.raw p level) (.Ok ()))
   (tail : Cut p next rest after (reply,final,calls)) :
   Cut p next (level::rest) before (reply,final,level::calls)

theorem source (p : Sized) (next : U64) (levels : List (Fin 20))
 (before : Frontier) (out : Reply × Frontier × List (Fin 20))
 (cut : Cut p next levels before out) :
 out=NKF_LaneTrace.run NLK_LaneTable.empty (NLK_LaneLoop.occupied next)
  (NLK_LaneLoop.raw p) levels before := by
 induction cut with
 | empty before => rfl
 | rejected level rest before after e one =>
   have h := NKP_LaneCuts.iteration (NLK_LaneTable.empty level) (NLK_LaneLoop.occupied next level)
    before after level (NLK_LaneLoop.raw p level) (.Err e) one
   rw [NKF_LaneTrace.run,←h]
 | continued level rest before after final reply calls one tail ih =>
   have h := NKP_LaneCuts.iteration (NLK_LaneTable.empty level) (NLK_LaneLoop.occupied next level)
    before after level (NLK_LaneLoop.raw p level) (.Ok ()) one
   rw [NKF_LaneTrace.run,←h]
   dsimp only
   rw [←ih]

#print source
#print axioms source
end NLK_LaneTrace
