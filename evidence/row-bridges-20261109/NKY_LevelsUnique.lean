import NKY_CanonicalLift
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKY_LevelsUnique
open Aeneas Aeneas.Std Result
open NJX_AppendDomains (Frontier High)
open NJX_DigestCohort (O)
open FIv_NativeValue (decode)
/-- Any valid CLOSED234 packet returns this full four-cell carrier. -/
theorem child {index level frontier o high}
 (p : NKI_AppendPacket.Packet index level frontier o high) :
 NKI_AppendPacket.cohort index level frontier o high=ok (NKI_AppendPacket.output p) := by
 simp only [NKI_AppendPacket.cohort,p.expected_call,p.association,bind_tc_ok]
 rfl

theorem child_unique {index level frontier o high}
 (p q : NKI_AppendPacket.Packet index level frontier o high) :
 NKI_AppendPacket.output p=NKI_AppendPacket.output q :=
 Result.ok.inj ((child p).symm.trans (child q))

theorem sum_model (index : U64) (f : Frontier) (o : O) (s : High)
 (p : NKI_LevelsChildren.Family index f o s) (j : Fin 4) :
 NKI_LevelsCohort.model index f o s p j=
 ((List.finRange 20).map (fun i=>decode (NKI_AppendPacket.output (p i) j))).sum := by
 rw [NKI_LevelsCohort.model,NKI_PackSum.source]
 congr 1
 apply List.map_congr_left
 intro i _hi
 exact (NKI_AppendMeaning.source (p i) j).symm

/-- The adopted value and its literal canonical carrier do not depend on the
existential packet witnesses chosen for the SAME input arguments. -/
theorem model_unique (index : U64) (f : Frontier) (o : O) (s : High)
 (p q : NKI_LevelsChildren.Family index f o s) :
 NKI_LevelsCohort.model index f o s p=NKI_LevelsCohort.model index f o s q := by
 funext j
 rw [sum_model,sum_model]
 congr 1
 apply List.map_congr_left
 intro i _hi
 rw [child_unique (p i) (q i)]

theorem literal_unique (index : U64) (f : Frontier) (o : O) (s : High)
 (p q : NKI_LevelsChildren.Family index f o s) :
 NKY_CanonicalLift.cohort index f o s p=NKY_CanonicalLift.cohort index f o s q := by
 unfold NKY_CanonicalLift.cohort
 rw [model_unique index f o s p q]
#print axioms child
#print axioms child_unique
#print axioms sum_model
#print axioms model_unique
#print axioms literal_unique
end AspisR1.NKY_LevelsUnique
end
