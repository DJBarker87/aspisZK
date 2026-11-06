import NKI_LevelsRoot
import NKI_AppendMeaning
import NKI_PackSum
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_LevelsCohort
open Aeneas Aeneas.Std Result
open FIv_NativeValue (Canon decode K)
open NJX_DigestCohort (O dc)
open NJX_AppendDomains (Frontier High)
open NJX_AppendFold (State)
def model (index : U64) (f : Frontier) (o : O) (s : High)
 (packets : NKI_LevelsChildren.Family index f o s) (j : Fin 4) : K :=
 NJB_PackLinearity.pack (fun k=>((List.finRange 20).map (fun i=>NKI_AppendMeaning.contribution (packets i) j k)).sum)
/-- Exact4cell decoded association: pack AFTER the entire old8lane sum is
identical to the new sum of packs. ZERO initialization is included. -/
theorem association (index : U64) (f : Frontier) (o : O) (s : High)
 (packets : NKI_LevelsChildren.Family index f o s) (out : State)
 (values : ∀ j,decode (out j)=((List.finRange 20).map (fun i=>decode (NKI_AppendPacket.output (packets i) j))).sum) :
 ∀ j,decode (out j)=model index f o s packets j := by
 intro j
 rw [values,model,NKI_PackSum.source]
 congr 1
 apply List.map_congr_left
 intro i hi
 exact NKI_AppendMeaning.source (packets i) j
#print axioms association
end AspisR1.NKI_LevelsCohort
end
