import PV_FN_THREAD_f6Provider124Dispatch
import PV_FN_THREAD_f6Provider126NativeJoin
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6OriginalTable
open PV_STX2_Syntax

/-- One source resolver for both ScopeData124 and Packet124, with all emitted
constructor and dereference dispositions. No table is changed at a call site.
This supplies only the resolver component of an original machine. -/
def programs (P : Data → Option PV_STX2_SliceSyntax.Program)
    (fn : Data) : Option PV_STX2_SliceSyntax.Program := by
  classical
  exact if fn = PV_THR2_ScopeArcCall.fn then some PV_THR2_F124.live else
    PV_THR2_PacketDataTable.resolve (PV_THR2_PacketInner320.resolve
      (PV_THR2_PacketConstructorLocalTable.table (PV_THR2_PacketOriginalTable.table P))) fn

/-- Both source instantiations of Arc::new resolve to the SAME emitted body. -/
theorem at124 (P : Data → Option PV_STX2_SliceSyntax.Program) :
    programs P PV_THR2_ScopeArcCall.fn = some PV_THR2_F124.live ∧
    programs P PV_THR2_Source361PacketChildren.fn58 = some PV_THR2_F124.live := by
  constructor
  · simp only [programs,ite_true]
  · rw [programs,if_neg PV_FN_THREAD_f6Provider124Dispatch.distinct124.symm]
    exact PV_THR2_PacketOriginalTable.at124 P

/-- Installing126/222/opaque320 on the selected source table is idempotent.
Hence every reached token, not merely an endpoint call, has identical resolution.
The exact source124 exception has id124 and cannot interfere with these rows. -/
theorem deref_fixed (P : Data → Option PV_STX2_SliceSyntax.Program) :
    PV_THR2_PacketDataTable.resolve (PV_THR2_PacketInner320.resolve (programs P)) = programs P := by
  funext fn
  unfold PV_THR2_PacketDataTable.resolve PV_THR2_PacketInner320.resolve
  cases h : PV_THR2_OffPath.functionId fn with
  | none => simp only [h]
  | some id =>
    by_cases h126 : id = 126
    · subst id
      have other : fn ≠ PV_THR2_ScopeArcCall.fn := by
        intro equal
        rw [equal] at h
        cases h
      simp only [h,programs,if_neg other,PV_THR2_PacketDataTable.resolve,
        PV_THR2_PacketInner320.resolve,h]
    · by_cases h222 : id = 222
      · subst id
        have other : fn ≠ PV_THR2_ScopeArcCall.fn := by
          intro equal
          rw [equal] at h
          cases h
        simp only [h,programs,if_neg other,PV_THR2_PacketDataTable.resolve,
          PV_THR2_PacketInner320.resolve,h]
      · by_cases h320 : id = 320
        · subst id
          have other : fn ≠ PV_THR2_ScopeArcCall.fn := by
            intro equal
            rw [equal] at h
            cases h
          simp only [h,programs,if_neg other,PV_THR2_PacketDataTable.resolve,
            PV_THR2_PacketInner320.resolve,h]
        · simp [h,h126,h222,h320]

/-- Literal provider definition: its local126 resolver agrees on EVERY token
when instantiated with the one source table. Handler agreement remains separate. -/
theorem local126_programs {E : Type}
    (x : PV_FN_THREAD_f126_ReturnedStage.Input E)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (source : x.P = programs P) :
    PV_FN_THREAD_f126_ReturnedStage.programs x = programs P := by
  unfold PV_FN_THREAD_f126_ReturnedStage.programs
  rw [source,deref_fixed]

/-- The constructor cone's seven emitted function ids have fixed dispositions
in both tables, independently of fallback and caller data. Coverage of actual
reached requests still has to be derived before applying prefix_identity. -/
theorem constructor_callees
    (P Q : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data) (id : Nat)
    (issued : PV_THR2_OffPath.functionId fn = some id)
    (member : id ∈ [121,216,217,218,312,313,315]) :
    programs P fn = PV_THR2_PacketConstructorLocalTable.table
      (PV_THR2_PacketOriginalTable.table Q) fn := by
  have different : id ≠ 124 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h | h | h | h | h | h | h <;> omega
  have other : fn ≠ PV_THR2_ScopeArcCall.fn := by
    intro equal
    rw [equal] at issued
    have eq : 124 = id := Option.some.inj issued
    exact different eq.symm
  rw [programs,if_neg other]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h | h | h | h | h | h | h <;> subst id <;>
    simp only [PV_THR2_PacketDataTable.resolve,PV_THR2_PacketInner320.resolve,
      PV_THR2_PacketConstructorLocalTable.table,issued]

/-- The seven function dispositions above agree with the provider's literal
local124 resolver, with no representation interface restated by the consumer. -/
theorem local124_programs
    (x : PV_FN_THREAD_f124_BoxContract.Input PV_RJ4IDB.NativeEvent)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (fn : Data) (id : Nat)
    (issued : PV_THR2_OffPath.functionId fn = some id)
    (member : id ∈ [121,216,217,218,312,313,315]) :
    programs P fn = PV_FN_THREAD_f124_Continuation.programs x fn := by
  exact constructor_callees P x.P fn id issued member

/-- The actual constructor allocation remains the emitted opaque BoxNew.
Only a resolver disposition is established; no allocation answer is fixed. -/
theorem atBox (P : Data → Option PV_STX2_SliceSyntax.Program) :
    programs P PV_THR2_Packet124BoxIssue17.fn = none := by
  have other : PV_THR2_Packet124BoxIssue17.fn ≠ PV_THR2_ScopeArcCall.fn := by
    intro equal
    have bad := congrArg PV_THR2_OffPath.functionId equal
    cases bad
  rw [programs,if_neg other]
  exact PV_THR2_PacketConstructorLocalTable.atBox P

#print axioms at124
#print axioms deref_fixed
#print axioms local126_programs
#print axioms constructor_callees
#print axioms local124_programs
#print axioms atBox
end PV_FN_THREAD_f6OriginalTable
