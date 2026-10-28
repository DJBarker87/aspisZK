import NDO_JFt_Digest22
import NDO_JFt_Digest23
import NDO_JFt_Digest24
import NDO_JFt_Digest25
import NDO_JFt_Digest26
import NDO_JFt_Digest27
import NDO_JFt_Digest28
import NDO_JFt_Digest29
import NDO_JFt_Digest30
import NDO_JFt_Digest31
import NDO_JFt_Digest32
import NDO_JFt_Digest33
import NDO_JFt_Digest34
import NDO_JFt_Digest35
import NDO_JFt_Digest36
import NDO_JFt_Digest37
import NDO_JFt_Digest38
import NDO_JFt_Digest39
import NDO_JFt_Digest40
import NDO_JFt_Digest41
import NDO_JFt_Digest42
import NDO_JFu_AfterstateValidator
set_option autoImplicit false
namespace AspisR1.JFt_AfterstateValue
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_terminal

def value : PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=14#u64,next_root:=JFt_Digest22.value,
   next_frontier:=Array.make 20#usize [JFt_Digest23.value,JFt_Digest24.value,JFt_Digest25.value,JFt_Digest26.value,JFt_Digest27.value,JFt_Digest28.value,JFt_Digest29.value,JFt_Digest30.value,JFt_Digest31.value,JFt_Digest32.value,JFt_Digest33.value,JFt_Digest34.value,JFt_Digest35.value,JFt_Digest36.value,JFt_Digest37.value,JFt_Digest38.value,JFt_Digest39.value,JFt_Digest40.value,JFt_Digest41.value,JFt_Digest42.value]}

theorem frontier : ∀ i : Fin 20,JFu_DigestCanonical.Canonical
    (value.next_frontier.val[i.val]'(by simp only [value,Array.make];exact i.isLt)) := by
  intro i
  fin_cases i
  · exact JFt_Digest23.canonical
  · exact JFt_Digest24.canonical
  · exact JFt_Digest25.canonical
  · exact JFt_Digest26.canonical
  · exact JFt_Digest27.canonical
  · exact JFt_Digest28.canonical
  · exact JFt_Digest29.canonical
  · exact JFt_Digest30.canonical
  · exact JFt_Digest31.canonical
  · exact JFt_Digest32.canonical
  · exact JFt_Digest33.canonical
  · exact JFt_Digest34.canonical
  · exact JFt_Digest35.canonical
  · exact JFt_Digest36.canonical
  · exact JFt_Digest37.canonical
  · exact JFt_Digest38.canonical
  · exact JFt_Digest39.canonical
  · exact JFt_Digest40.canonical
  · exact JFt_Digest41.canonical
  · exact JFt_Digest42.canonical

theorem validated : validate_verified_afterstate value=ok (.Ok ()) :=
  JFu_AfterstateValidator.source value (by decide) (by decide) JFt_Digest22.canonical frontier

#print axioms frontier
#print axioms validated
end AspisR1.JFt_AfterstateValue
