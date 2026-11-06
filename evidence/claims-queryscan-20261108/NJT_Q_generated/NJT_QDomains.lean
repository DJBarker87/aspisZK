import NJT_QScan
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJT_QDomains
open Aeneas Aeneas.Std Result NJT_QBase
open Query31ExplicitListLoop

def Domain (s : State) : Prop :=
 validState s ∧ NHB_Canonical.State s ∧ NHB_Inactive.State s

theorem initial : Domain NGQ_SamplerPacket.initial :=
 ⟨NGQ_SamplerPacket.initial_valid,NHB_Canonical.initial,NHB_Inactive.initial⟩

/-- Every native word caller retains the exact membership domains. This uses
native/model step equality at the same prestate, not a successful final sample. -/
theorem preserved (native : NJT_QScan.Native) (cut : NJT_QScan.Cut native)
 (xs : List U32) (s : State) (domain : Domain s)
 (canonical : ∀ x∈xs,x.val<262144) :
 Domain (NJT_QScan.run native xs s).1 := by
 obtain ⟨final,pending,edges,good⟩:=NGQ_SamplerConstruct.construct xs s domain.1
 obtain ⟨cursor,trace⟩:=NHK_WordAssociation.records edges 0
 rw [NJT_QScan.trace native cut edges domain.1]
 exact ⟨good,NHB_Canonical.word_invariant trace domain.2.1 canonical,
  NHB_Inactive.word_invariant trace domain.2.2⟩

theorem scan_preserved (native : NJT_QScan.Native) (cut : NJT_QScan.Cut native)
 (b : Bytes) (s : State) (domain : Domain s) :
 Domain (NJT_QScan.run native (words b).val s).1 :=
 preserved native cut _ s domain (NHB_Canonical.decoded b _ (words_source b))

/-- No state-validity premise escapes the actual initial private call. Later
calls use scan_preserved. This is a complete Bool and mutable-state Result. -/
theorem initial_scan (native : NJT_QScan.Native) (cut : NJT_QScan.Cut native) (b : Bytes) :
 Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords
  NGQ_SamplerPacket.initial b=
  ok (optionStop (NJT_QScan.run native (words b).val NGQ_SamplerPacket.initial).2,
    (NJT_QScan.run native (words b).val NGQ_SamplerPacket.initial).1) :=
 NJT_QScan.scan native cut _ initial.1 b

/-- Every continuing membership invocation lies in precisely0..21, with the
canonical/inactive clauses needed by the retained16/18/19 native certificates. -/
theorem membership_domain (s : State) (domain : Domain s)
 (notFull : s.accepted_len.val≠22) (notLimit : s.draws.val≠64) :
 s.accepted_len.val<22 ∧ s.draws.val<64 ∧ NHB_Canonical.State s ∧ NHB_Inactive.State s := by
 have hlen:=domain.1.1
 have hdraw:=domain.1.2.1
 exact ⟨by omega,by omega,domain.2⟩

#print axioms initial
#print axioms preserved
#print axioms scan_preserved
#print axioms initial_scan
#print axioms membership_domain
#check @initial_scan
end AspisR1.NJT_QDomains
end
