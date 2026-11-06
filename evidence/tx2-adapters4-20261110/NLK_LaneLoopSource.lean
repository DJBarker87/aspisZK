import NLK_LaneLoop
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NLK_LaneLoopSource
open Aeneas Aeneas.Std Result NKP_LaneCuts
abbrev Sized := NLK_LaneInput.Sized

def one (p : Sized) (next : U64) (before : Frontier) (level : Fin 20) :
 Result (Reply × Frontier) := do
 let raw ← NLK_LaneDigest.source (NLK_LaneInput.frontier p level)
 ok (NKF_LaneTrace.iteration (NLK_LaneTable.empty level)
     (NLK_LaneLoop.occupied next level) before level raw)

theorem one_source (p : Sized) (next : U64) (before : Frontier) (level : Fin 20) :
 one p next before level=ok (NLK_LaneLoop.step p next before level) := by
 unfold one
 rw [NLK_LaneDigest.child]
 rfl

def run (p : Sized) (next : U64) :
 List (Fin 20) → Frontier → Result (Reply × Frontier × List (Fin 20))
 | [],before => ok (.Ok (),before,[])
 | level::rest,before => do
   let current ← one p next before level
   match current.1 with
   | .Err e => ok (.Err e,current.2,[level])
   | .Ok _ =>
    let tail ← run p next rest current.2
    ok (tail.1,tail.2.1,level::tail.2.2)

theorem source (p : Sized) (next : U64) (levels : List (Fin 20)) (before : Frontier) :
 run p next levels before = ok (NKP_LaneInduction.fold (NLK_LaneLoop.step p next) levels before) := by
 induction levels generalizing before with
 | nil => rfl
 | cons level rest ih =>
   simp only [run,one_source,bind_tc_ok,NKP_LaneInduction.fold]
   cases h : NLK_LaneLoop.step p next before level with
   | mk reply after =>
    simp only [h]
    cases reply with
    | Err e => rfl
    | Ok u => simp only [ih,bind_tc_ok]


#print one_source
#print axioms one_source
#print source
#print axioms source
end NLK_LaneLoopSource
