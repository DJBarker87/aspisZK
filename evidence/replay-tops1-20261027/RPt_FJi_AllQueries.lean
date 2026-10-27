import RPt_FJi_Query00
import RPt_FJi_Query01
import RPt_FJi_Query02
import RPt_FJi_Query03
import RPt_FJi_Query04
import RPt_FJi_Query05
import RPt_FJi_Query06
import RPt_FJi_Query07
import RPt_FJi_Query08
import RPt_FJi_Query09
import RPt_FJi_Query10
import RPt_FJi_Query11
import RPt_FJi_Query12
import RPt_FJi_Query13
import RPt_FJi_Query14
import RPt_FJi_Query15
import RPt_FJi_Query16
import RPt_FJi_Query17
import RPt_FJi_Query18
import RPt_FJi_Query19
import RPt_FJi_Query20
import RPt_FJi_Query21
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_AllQueries
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody
abbrev E := FIp_DotsAdapter.E
def index (j : Fin 22) : Usize := Usize.ofNat j.val (by have:=j.isLt;scalar_tac)
/-- Fin22 induction; each child meaning comes from its OWN actual source call
and all calls retain the SAME proof and selected width29 powers. This does
not yet derive the model W/V/gamma identities or match0. -/
theorem value (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a : Fin 22 → verifier.Accumulator) (g : Array E 29#usize)
    (obs : Option (verifier.Phase → Result Unit))
    (geometry : Fin 22 → verifier.QueryGeometry) (pending : Fin 22 → verifier.BatchedWeights)
    (answer : Fin 22 → core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)
    (installed : ops.op20=FIp_DotsAdapter.dots)
    (hg : FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray g))
    (runs : ∀ j,verifier.candidate.query_values ops proof p {(a j) with next:=index j}
      g obs (geometry j) (pending j)=ok (answer j)) :
    ∀ j,FJi_QueryJoin.Meaning ops proof (index j) g := by
  intro j
  induction j using Fin.induction with
  | zero =>
    exact FJi_Query00.value ops proof p (a 0) g obs (geometry 0) (pending 0) (answer 0) installed hg (runs 0)
  | succ k ih =>
    fin_cases k
    · exact FJi_Query01.value ops proof p (a 1) g obs (geometry 1) (pending 1) (answer 1) installed hg (runs 1)
    · exact FJi_Query02.value ops proof p (a 2) g obs (geometry 2) (pending 2) (answer 2) installed hg (runs 2)
    · exact FJi_Query03.value ops proof p (a 3) g obs (geometry 3) (pending 3) (answer 3) installed hg (runs 3)
    · exact FJi_Query04.value ops proof p (a 4) g obs (geometry 4) (pending 4) (answer 4) installed hg (runs 4)
    · exact FJi_Query05.value ops proof p (a 5) g obs (geometry 5) (pending 5) (answer 5) installed hg (runs 5)
    · exact FJi_Query06.value ops proof p (a 6) g obs (geometry 6) (pending 6) (answer 6) installed hg (runs 6)
    · exact FJi_Query07.value ops proof p (a 7) g obs (geometry 7) (pending 7) (answer 7) installed hg (runs 7)
    · exact FJi_Query08.value ops proof p (a 8) g obs (geometry 8) (pending 8) (answer 8) installed hg (runs 8)
    · exact FJi_Query09.value ops proof p (a 9) g obs (geometry 9) (pending 9) (answer 9) installed hg (runs 9)
    · exact FJi_Query10.value ops proof p (a 10) g obs (geometry 10) (pending 10) (answer 10) installed hg (runs 10)
    · exact FJi_Query11.value ops proof p (a 11) g obs (geometry 11) (pending 11) (answer 11) installed hg (runs 11)
    · exact FJi_Query12.value ops proof p (a 12) g obs (geometry 12) (pending 12) (answer 12) installed hg (runs 12)
    · exact FJi_Query13.value ops proof p (a 13) g obs (geometry 13) (pending 13) (answer 13) installed hg (runs 13)
    · exact FJi_Query14.value ops proof p (a 14) g obs (geometry 14) (pending 14) (answer 14) installed hg (runs 14)
    · exact FJi_Query15.value ops proof p (a 15) g obs (geometry 15) (pending 15) (answer 15) installed hg (runs 15)
    · exact FJi_Query16.value ops proof p (a 16) g obs (geometry 16) (pending 16) (answer 16) installed hg (runs 16)
    · exact FJi_Query17.value ops proof p (a 17) g obs (geometry 17) (pending 17) (answer 17) installed hg (runs 17)
    · exact FJi_Query18.value ops proof p (a 18) g obs (geometry 18) (pending 18) (answer 18) installed hg (runs 18)
    · exact FJi_Query19.value ops proof p (a 19) g obs (geometry 19) (pending 19) (answer 19) installed hg (runs 19)
    · exact FJi_Query20.value ops proof p (a 20) g obs (geometry 20) (pending 20) (answer 20) installed hg (runs 20)
    · exact FJi_Query21.value ops proof p (a 21) g obs (geometry 21) (pending 21) (answer 21) installed hg (runs 21)
#print axioms value
end AspisR1.FJi_AllQueries
end
