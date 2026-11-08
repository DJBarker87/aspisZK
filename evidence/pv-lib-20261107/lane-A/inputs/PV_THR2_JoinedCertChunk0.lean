import PV_THR2_FreshSyntaxCertificate
import PV_THR2_JoinedCertDescriptor
import PV_THR2_MatchExecutionShape
import PV_THR2_QuietTraceCertificate

set_option autoImplicit false
namespace PV_THR2_JoinedCertDispatchTrace
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_IntrinsicState
/-- Proof-local descriptor exclusions on the retained finite source composition.
No exclusion is an OwnInit hypothesis or a global reachable-control invariant. -/
def Certificate {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (n : Nat) (s : State W E) : Prop :=
  ∀ k, k < n → PV_THR2_JoinedCertDescriptor.Clear (advance B K P H k s)
/-- Conditional on amended-translator acceptance. Internal next-instruction fact. -/
theorem one {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : State W E) (clear : PV_THR2_JoinedCertDescriptor.Clear s) :
    Certificate B K P H 1 s := by
  intro k hk
  have zero : k = 0 := by omega
  subst k
  exact clear
/-- Conditional on amended-translator acceptance. Append certificates at the
existing named source result; no transition or source-store equality is re-proved. -/
theorem append {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (n m : Nat) (s t : State W E)
    (reached : advance B K P H n s = t)
    (first : Certificate B K P H n s) (tail : Certificate B K P H m t) :
    Certificate B K P H (n+m) s := by
  intro k hk
  by_cases before : k < n
  · exact first k before
  · have h := tail (k-n) (by omega)
    have offset : k = n+(k-n) := by omega
    rw [offset,PV_THR2_IntrinsicComposition.advance_add,reached]
    exact h
/-- Conditional on amended-translator acceptance. A retained actual gap is
fixed by the already proved machine law; all descriptor exclusions are vacuous. -/
theorem gap {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (n : Nat) (s : State W E) (site : Option Site) (store : Store Data)
    (h : s.current.status = .undefined site store) : Certificate B K P H n s := by
  intro k hk
  rw [PV_THR2_QuietTraceCertificate.gap_fixed B K P H k s site store h]
  intro c running
  rw [h] at running
  cases running
#print axioms one
#print axioms append
#print axioms gap
end PV_THR2_JoinedCertDispatchTrace

set_option autoImplicit false
namespace PV_THR2_JoinedCertDispatchShapes
open Aeneas Aeneas.Std PV_STX2_Syntax PV_STX2_SliceMachine
/-- Internal source instruction fact, independent of stores and operands. -/
theorem fresh (c : Config) (h : c.frame.waiting = none) :
    ∀ wait fn a args, c.frame.waiting = some wait →
      wait.request = .child fn a args →
      fn ≠ PV_THR2_Source361PacketChildren.fn58 ∧
      fn ≠ PV_THR2_PacketDataTable.fn126 ∧ fn ≠ⱼ PV_THR2_PacketDataTable.fn222 := by
  intro wait fn a args saved request
  rw [h] at saved
  cases saved
/-- A known saved source descriptor excludes the three exact Packet calls by
its emitted identity. The inequalities are internal syntax proofs only. -/
theorem child (c : Config) (wait : PV_STX2_Native.Waiting Data)
    (fn : Data) (a : Nat) (args : List Data)
    (saved : c.frame.waiting = some wait) (request : wait.request = .child fn a args)
    (not124 : fn ≠ PV_THR2_Source361PacketChildren.fn58)
    (not126 : fn ≠ PV_THR2_PacketDataTable.fn126)
    (not222 : fn ≠ⱼ PV_THR2_PacketDataTable.fn222) :
    ∀ other callee activation values, c.frame.waiting = some other → other.request = .child callee activation values →
      callee ≠ PV_THR2_Source361PacketChildren.fn58 ∧
      callee ≠ PV_THR2_PacketDataTable.fn126 ∧ callee ≠ⱼ PV_THR2_PacketDataTable.fn222 := by
  intro other callee activation values waiting requested
  have eq : other = wait := Option.some.inj (waiting.symm.trans saved)
  subst other
  rw [request] at requested
  cases requested
  exact ⟨not124,not126,not222⟩
#print axioms fresh
#print axioms child
end PV_THR2_JoinedCertDispatchShapes

set_option autoImplicit false
namespace PV_THR2_JoinedCertDispatchQuiet
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_IntrinsicState PV_THR2_JoinedCertDispatchTrace PV_THR2_QuietInstructionShape
/-- Conditional on amended-translator acceptance. Hypotheses: existing Quiet
instruction shape and a fresh source frame. One symbolic induction uses the
retained QuietExecutionShape and QuietStatusRange lemmas BY NAME. No original
source execution is re-proved. This certifies only table independence along
that segment, including its failed operands and its next fresh instruction. -/
theorem quiet_prefix {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (nodes : List Instruction) (tail : List PV_STX2_SliceSyntax.Node)
    (c : Config) (w : W) (es : List E) (stack : List Config)
    (done : c.frame.completed = none) (waiting : c.frame.waiting = none)
    (remaining : c.frame.remaining = nodes.map PV_STX2_SliceSyntax.Node.leaf ++ tail)
    (quiet : ∀ i, i ∈ nodes → Quiet i) :
    Certificate base ctl programs handler (nodes.length+1) ⟨⟨.running c,w,es⟩,stack⟩ := by
  induction nodes generalizing c w es with
  | nil =>
    apply PV_THR2_JoinedCertDispatchTrace.one
    intro d running
    cases running
    exact PV_THR2_JoinedCertDispatchShapes.fresh c waiting
  | cons i nodes ih =>
    have qi : Quiet i := quiet i (List.mem_cons.mpr (Or.inl rfl))
    have shape : c.frame.remaining = .leaf i :: (nodes.map PV_STX2_SliceSyntax.Node.leaf ++ tail) := by
      simpa only [List.map_cons,List.cons_append] using remaining
    let table := programs
    let q := PV_THR2_Execution.step base ctl table handler c w
    have post := PV_THR2_QuietExecutionShape.step base ctl table handler c w i _ done waiting shape qi
    have range := PV_THR2_QuietStatusRange.execution base ctl table handler c w i _ done waiting shape qi
    have reached : PV_THR2_IntrinsicState.advance base ctl table handler 1
        ⟨⟨.running c,w,es⟩,stack⟩ = ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
      simp only [PV_THR2_IntrinsicState.advance]
      exact PV_THR2_IntrinsicCompatible.step base ctl table handler c w es stack
        (PV_THR2_IntrinsicCompatible.not_waiting c waiting)
    have first : Certificate base ctl programs handler 1 ⟨⟨.running c,w,es⟩,stack⟩ := by
      apply PV_THR2_JoinedCertDispatchTrace.one
      intro d running
      cases running
      exact PV_THR2_JoinedCertDispatchShapes.fresh c waiting
    have second : Certificate base ctl programs handler (nodes.length+1)
        ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
      cases status : q.status with
      | running d =>
        obtain ⟨nextDone,nextWaiting,nextRemaining⟩ := post d status
        exact ih d q.world (es ++ q.events) nextDone nextWaiting nextRemaining
          (by intro j hj; exact quiet j (List.mem_cons_of_mem i hj))
      | undefined site store =>
        apply gap base ctl programs handler (nodes.length+1) _ site store
        rfl
      | returned r store =>
        have bad : False := by
          change PV_THR2_QuietStatusRange.Range q.status at range
          simpa only [status,PV_THR2_QuietStatusRange.Range] using range
        exact False.elim bad
      | fault f store =>
        have bad : False := by
          change PV_THR2_QuietStatusRange.Range q.status at range
          simpa only [status,PV_THR2_QuietStatusRange.Range] using range
        exact False.elim bad
    have total := PV_THR2_JoinedCertDispatchTrace.append base ctl programs handler
      1 (nodes.length+1) _ _ reached first second
    have length : 1+(nodes.length+1) = (i::nodes).length+1 := by simp only [List.length_cons]; omega
    rw [length] at total
    exact total
#print axioms quiet_prefix
end PV_THR2_JoinedCertDispatchQuiet

set_option autoImplicit false
namespace PV_THR2_JoinedCertDispatchWrapped
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_IntrinsicState PV_THR2_QuietInstructionShape
/-- Name the original table under which the retained prefix was proved. -/
def table (P : Data → Option PV_STX2_SliceSyntax.Program) :=
  PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve P)
/-- Internal exact-Packet exclusion certificate on the UNCHANGED original trace. -/
abbrev Certificate {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data) :=
  PV_THR2_JoinedCertDispatchTrace.Certificate B K (table P) H
/-- Internal one-step source-shape fact; no endpoint hypothesis. -/
theorem one {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : State W E) (clear : PV_THR2_JoinedCertDescriptor.Clear s) :
    Certificate B K P H 1 s := PV_THR2_JoinedCertDispatchTrace.one B K (table P) H s clear
/-- Consume the existing named original-source boundary; append only the new
local descriptor exclusions. No source transition is re-proved. -/
theorem append {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (n m : Nat) (s t : State W E)
    (reached : advance B K (table P) H n s = t)
    (first : Certificate B K P H n s) (tail : Certificate B K P H m t) :
    Certificate B K P H (n+m) s :=
  PV_THR2_JoinedCertDispatchTrace.append B K (table P) H n m s t reached first tail
/-- A failed source operand stays in its retained interpretation gap. -/
theorem gap {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (n : Nat) (s : State W E) (site : Option Site) (store : Store Data)
    (h : s.current.status = .undefined site store) : Certificate B K P H n s :=
  PV_THR2_JoinedCertDispatchTrace.gap B K (table P) H n s site store h
/-- Use existing source syntax and Quiet proofs BY NAME. This changes only the
property certified, to the three exact Packet descriptors; all operands remain
abstract, and the already proved source execution is not repeated. -/
theorem quiet_prefix {W E : Type} (B : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (nodes : List Instruction) (tail : List PV_STX2_SliceSyntax.Node)
    (c : Config) (w : W) (es : List E) (stack : List Config)
    (done : c.frame.completed = none) (waiting : c.frame.waiting = none)
    (remaining : c.frame.remaining = nodes.map PV_STX2_SliceSyntax.Node.leaf ++ tail)
    (quiet : ∀ i, i ∈ nodes → Quiet i) :
    Certificate B K P H (nodes.length+1) ⟨⟨.running c,w,es⟩,stack⟩ :=
  PV_THR2_JoinedCertDispatchQuiet.quiet_prefix B K (table P) H nodes tail c w es stack
    done waiting remaining quiet
#print axioms one
#print axioms append
#print axioms gap
#print axioms quiet_prefix
end PV_THR2_JoinedCertDispatchWrapped

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertConfiguration
open PV_STX2_Syntax PV_STX2_SliceMachine
/-- Internal next-instruction shape; no closure hypothesis. -/
def Ordinary (c : Config) : Prop :=
  ∀ wait fn a args, c.frame.waiting = some wait →
    wait.request = .child fn a args → fn ≠ PV_THR2_Source361PacketChildren.fn58 ∧ fn ≠ PV_THR2_PacketDataTable.fn126 ∧ fn ≠ⱼ PV_THR2_PacketDataTable.fn222
end PV_THR2_JoinedCertCertConfiguration

set_option autoImplicit false
namespace PV_THR2_JoinedCertCertFreshSyntaxCertificate
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
abbrev Fresh := PV_THR2_FreshSyntaxCertificate.Fresh
/-- Conditional on amended-translator acceptance. Internal syntax certificate
for the retained original composition; all stores, operands and native outcomes
remain arbitrary. The original source run is reused, never re-proved. Excludes
the exact Packet descriptors and joined constructor/native dispositions; no endpoint premise. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (n : Nat) (nodes : List PV_STX2_SliceSyntax.Node) (safe : Fresh n nodes)
    (c : Config) (w : W) (es : List E) (stack : List Config)
    (done : c.frame.completed = none) (waiting : c.frame.waiting = none)
    (remaining : c.frame.remaining = nodes) :
    PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler n
      ⟨⟨.running c,w,es⟩,stack⟩ := by
  induction safe generalizing c w es with
  | zero => intro k hk; omega
  | one =>
    apply PV_THR2_JoinedCertDispatchWrapped.one
    intro d h
    cases h
    exact PV_THR2_JoinedCertDispatchShapes.fresh c waiting
  | @quiet n i rest shape tail ih =>
    let table := PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)
    let q := PV_THR2_Execution.step base ctl table handler c w
    have post := PV_THR2_QuietExecutionShape.step base ctl table handler c w i rest done waiting remaining shape
    have range := PV_THR2_QuietStatusRange.execution base ctl table handler c w i rest done waiting remaining shape
    have reached : PV_THR2_IntrinsicState.advance base ctl table handler 1
        ⟨⟨.running c,w,es⟩,stack⟩ = ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
      simp only [PV_THR2_IntrinsicState.advance]
      exact PV_THR2_IntrinsicCompatible.step base ctl table handler c w es stack
        (PV_THR2_IntrinsicCompatible.not_waiting c waiting)
    have first : PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 1 ⟨⟨.running c,w,es⟩,stack⟩ := by
      apply PV_THR2_JoinedCertDispatchWrapped.one
      intro d h
      cases h
      exact PV_THR2_JoinedCertDispatchShapes.fresh c waiting
    have second : PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler n
        ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
      change PV_THR2_QuietStatusRange.Range q.status at range
      cases status : q.status with
      | running d =>
        obtain ⟨hd,hw,hr⟩ := post d status
        exact ih d q.world (es ++ q.events) hd hw hr
      | undefined site store => exact PV_THR2_JoinedCertDispatchWrapped.gap base ctl programs handler n _ site store rfl
      | returned r store => simp only [status,PV_THR2_QuietStatusRange.Range] at range
      | fault f store => simp only [status,PV_THR2_QuietStatusRange.Range] at range
    have total := PV_THR2_JoinedCertDispatchWrapped.append base ctl programs handler 1 n _ _ reached first second
    simpa only [Nat.add_comm 1 n] using total
  | @matching n site place arms otherwise rest armsSafe ih =>
    let table := PV_THR2_CatchTakeChild.table (PV_THR2_SourceTraitDispatch.resolve programs)
    let q := PV_THR2_Execution.step base ctl table handler c w
    let P := fun (nodes : List PV_STX2_SliceSyntax.Node) =>
      ∀ (d : Config) (v : W) (events : List E), d.frame.completed = none →
      d.frame.waiting = none → d.frame.remaining = nodes →
      PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler n
        ⟨⟨.running d,v,events⟩,stack⟩
    have selected : ∀ tag body, selectVariant tag arms otherwise = some body → P (body ++ rest) := by
      intro tag body h d v events hd hw hr
      exact ih tag body h d v events hd hw hr
    obtain ⟨range,post⟩ := PV_THR2_MatchExecutionShape.step base ctl table handler c w site place arms otherwise rest P selected done waiting remaining
    have reached : PV_THR2_IntrinsicState.advance base ctl table handler 1
        ⟨⟨.running c,w,es⟩,stack⟩ = ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
      simp only [PV_THR2_IntrinsicState.advance]
      exact PV_THR2_IntrinsicCompatible.step base ctl table handler c w es stack
        (PV_THR2_IntrinsicCompatible.not_waiting c waiting)
    have first : PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler 1 ⟨⟨.running c,w,es⟩,stack⟩ := by
      apply PV_THR2_JoinedCertDispatchWrapped.one
      intro d h
      cases h
      exact PV_THR2_JoinedCertDispatchShapes.fresh c waiting
    have second : PV_THR2_JoinedCertDispatchWrapped.Certificate base ctl programs handler n
        ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
      change PV_THR2_QuietStatusRange.Range q.status at range
      cases status : q.status with
      | running d =>
        obtain ⟨hd,hw,hr⟩ := post d status
        exact hr d q.world (es ++ q.events) hd hw rfl
      | undefined site store => exact PV_THR2_JoinedCertDispatchWrapped.gap base ctl programs handler n _ site store rfl
      | returned r store => simp only [status,PV_THR2_QuietStatusRange.Range] at range
      | fault f store => simp only [status,PV_THR2_QuietStatusRange.Range] at range
    have total := PV_THR2_JoinedCertDispatchWrapped.append base ctl programs handler 1 n _ _ reached first second
    simpa only [Nat.add_comm 1 n] using total
#print axioms run
end PV_THR2_JoinedCertCertFreshSyntaxCertificate
