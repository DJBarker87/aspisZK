import S4LiteralRow31PairsJoinV1
set_option autoImplicit false
namespace AspisR1.S4ScanOutRunCoreV1
open AspisV8R19.Q22WordScan AspisV8R19.SourceDuplexStep AspisV8R19.SamplerWords
/-- A finite scanner trace carrying the exact squeeze and advance lists. -/
inductive Run : Nat → ScanState → List State → List State → ScanState → State → State → Prop where
  | done (q : ScanState) (s : State) : Run 0 q [] [] q s s
  | stopped {n : Nat} {q qf : ScanState} {b : State} {bs : List State}
      {x initial : State} {xs : List State}
      (hguard : q.draws < 64)
      (hscan : scan q (words 18 b) = (qf, true))
      : Run (n+1) q (b::bs) (x::xs) qf initial x
  | continued {n : Nat} {q q' qf : ScanState} {b : State} {bs : List State}
      {x : State} {xs : List State} {s initial : State}
      (hguard : q.draws < 64)
      (hscan : scan q (words 18 b) = (q', false))
      (htail : Run n q' bs xs qf x s)
      : Run (n+1) q (b::bs) (x::xs) qf initial s

theorem scanOut_of_run : ∀ {n q bs xs qf initial final},
    Run n q bs xs qf initial final →
    R0C.V3.Q22.scanOut n q bs xs initial = (finish qf, final) := by
  intro n q bs xs qf initial final h
  induction h with
  | done q s => rfl
  | stopped hguard hscan =>
      simp [R0C.V3.Q22.scanOut, hguard, hscan]
  | continued hguard hscan htail ih =>
      simp [R0C.V3.Q22.scanOut, hguard, hscan, ih]
#print axioms scanOut_of_run
end AspisR1.S4ScanOutRunCoreV1
