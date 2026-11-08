import PV_LIB_A_ChainTrace11
import PV_THR2_IntrinsicFrameAggregate
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_SourceSequence13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

/-- Finite source administration including real aggregate moves. No calls or
cleanup nodes are erased; each actual use must prove its exact node list. -/
inductive Seq where
  | done
  | storage (site : PV_STX2_Syntax.Site) (live : Bool) (slot : Nat) (tail : Seq)
  | bind (site : PV_STX2_Syntax.Site) (dest : PV_STX2_Syntax.Place) (expr : Expr) (tail : Seq)
  | aggregate (site : PV_STX2_Syntax.Site) (dest : PV_STX2_Syntax.Place) (kind : Data) (args : List Operand) (tail : Seq)

def nodes : Seq → List PV_STX2_SliceSyntax.Node
  | .done => []
  | .storage site live slot tail => .leaf (.storage site live slot) :: nodes tail
  | .bind site dest expr tail => .leaf (.bind site dest expr) :: nodes tail
  | .aggregate site dest kind args tail => .leaf (.aggregateMove site dest kind args) :: nodes tail

def sites : Seq → Prop
  | .done => True
  | .storage site _ _ tail | .bind site _ _ tail | .aggregate site _ _ _ tail =>
      site.function ≠ 361 ∧ sites tail

abbrev bound := @PV_THR2_IntrinsicFrameChain.bound

def steps (C : Carrier OWNER Data) (a : Nat) (w : OWNER) : Seq → Store Data → Nat
  | .done,_ => 0
  | .storage _ _ slot tail,s => 1 + steps C a w tail (write s ⟨a,slot,[]⟩ none)
  | .bind _ dest expr tail,s => 1 + match bound C s a dest expr w with
      | none => 0 | some t => steps C a w tail t
  | .aggregate _ dest kind args tail,s => 1 + match bound C s a dest (.aggregate kind args) w with
      | none => 0 | some t => steps C a w tail t

def result (C : Carrier OWNER Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (w : OWNER) : Seq → Store Data → Status
  | .done,s => .running ⟨{activation := a,remaining := rest,loops := loops},parents,s⟩
  | .storage _ _ slot tail,s => result C a parents loops rest w tail (write s ⟨a,slot,[]⟩ none)
  | .bind site dest expr tail,s => match bound C s a dest expr w with
      | none => .undefined (some site) s | some t => result C a parents loops rest w tail t
  | .aggregate site dest kind args tail,s => match bound C s a dest (.aggregate kind args) w with
      | none => .undefined (some site) s | some t => result C a parents loops rest w tail t

theorem aggregate_quiet (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (site : PV_STX2_Syntax.Site) (dest : PV_STX2_Syntax.Place) (kind : Data) (args : List Operand)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    Quiet P ⟨⟨.running ⟨{activation := a,remaining := .leaf (.aggregateMove site dest kind args) :: rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ := by
  constructor
  · intro c hc; cases hc; rfl
  · intro c hc; cases hc; exact ⟨rfl,rfl,True.intro⟩

/-- Source run and quiet certificate are proved together by structural induction.
Unknown reads retain their gap/store; no native or allocator answer is chosen. -/
theorem certified (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler)
    (seq : Seq) (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) (off : sites seq) :
    let q : State := ⟨⟨.running ⟨{activation := a,remaining := nodes seq ++ rest,loops := loops},parents,s⟩,w,es⟩,stack⟩
    Trace C K P H (steps C a w seq s) q ∧
    PV_THR2_IntrinsicState.advance C K P H (steps C a w seq s) q =
      ⟨⟨result C a parents loops rest w seq s,w,es⟩,stack⟩ := by
  induction seq generalizing s with
  | done => exact ⟨True.intro,rfl⟩
  | storage site live slot tail ih =>
    simp only [nodes,List.cons_append,steps,result]
    have next := ih (write s ⟨a,slot,[]⟩ none) off.2
    constructor
    · apply append C K P H 1 _ _
        ⟨PV_LIB_A_ChainTrace11.storage_quiet P s a parents loops _ site live slot w es stack off.1,True.intro⟩
      rw [PV_THR2_IntrinsicFrameSteps.storage]; exact next.1
    · rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_IntrinsicFrameSteps.storage]; exact next.2
  | bind site dest expr tail ih =>
    simp only [nodes,List.cons_append,steps]
    have first := PV_THR2_IntrinsicFrameBind.run C K P H s a parents loops (nodes tail ++ rest) site dest expr w es stack
    constructor
    · apply append C K P H 1 _ _
        ⟨PV_LIB_A_ChainTrace11.bind_quiet P s a parents loops _ site dest expr w es stack off.1,True.intro⟩
      rw [first]
      change Trace C K P H (match bound C s a dest expr w with | none => 0 | some t => steps C a w tail t)
        (match bound C s a dest expr w with
        | none => ⟨⟨.undefined (some site) s,w,es⟩,stack⟩
        | some t => ⟨⟨.running ⟨{activation := a,remaining := nodes tail ++ rest,loops := loops},parents,t⟩,w,es⟩,stack⟩)
      cases hb : bound C s a dest expr w with
      | none => trivial
      | some t => exact (ih t off.2).1
    · rw [PV_THR2_IntrinsicComposition.advance_add,first]
      change PV_THR2_IntrinsicState.advance C K P H
        (match bound C s a dest expr w with | none => 0 | some t => steps C a w tail t)
        (match bound C s a dest expr w with
        | none => ⟨⟨.undefined (some site) s,w,es⟩,stack⟩
        | some t => ⟨⟨.running ⟨{activation := a,remaining := nodes tail ++ rest,loops := loops},parents,t⟩,w,es⟩,stack⟩) = _
      cases hb : bound C s a dest expr w with
      | none => simp only [result,hb]; rfl
      | some t => simpa only [result,hb] using (ih t off.2).2
  | aggregate site dest kind args tail ih =>
    simp only [nodes,List.cons_append,steps]
    have first := PV_THR2_IntrinsicFrameAggregate.run C K P H s a parents loops (nodes tail ++ rest) site dest kind args w es stack
    constructor
    · apply append C K P H 1 _ _ ⟨aggregate_quiet P s a parents loops _ site dest kind args w es stack,True.intro⟩
      rw [first]
      change Trace C K P H (match bound C s a dest (.aggregate kind args) w with | none => 0 | some t => steps C a w tail t)
        (match bound C s a dest (.aggregate kind args) w with
        | none => ⟨⟨.undefined (some site) s,w,es⟩,stack⟩
        | some t => ⟨⟨.running ⟨{activation := a,remaining := nodes tail ++ rest,loops := loops},parents,t⟩,w,es⟩,stack⟩)
      cases hb : bound C s a dest (.aggregate kind args) w with
      | none => trivial
      | some t => exact (ih t off.2).1
    · rw [PV_THR2_IntrinsicComposition.advance_add,first]
      change PV_THR2_IntrinsicState.advance C K P H
        (match bound C s a dest (.aggregate kind args) w with | none => 0 | some t => steps C a w tail t)
        (match bound C s a dest (.aggregate kind args) w with
        | none => ⟨⟨.undefined (some site) s,w,es⟩,stack⟩
        | some t => ⟨⟨.running ⟨{activation := a,remaining := nodes tail ++ rest,loops := loops},parents,t⟩,w,es⟩,stack⟩) = _
      cases hb : bound C s a dest (.aggregate kind args) w with
      | none => simp only [result,hb]; rfl
      | some t => simpa only [result,hb] using (ih t off.2).2

theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (seq : Seq) (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) (off : sites seq) :
    advance C K P resources encode H values (steps C a w seq s)
      ⟨⟨⟨.running ⟨{activation := a,remaining := nodes seq ++ rest,loops := loops},parents,s⟩,w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨result C a parents loops rest w seq s,w,es⟩,stack⟩,none⟩ := by
  rw [PV_LIB_A_PrefixMachine11.run C K P resources encode H values _ _
    (certified C K P H seq s a parents loops rest w es stack off).1,
    (certified C K P H seq s a parents loops rest w es stack off).2]

#print axioms aggregate_quiet
#print axioms certified
#print axioms run
end PV_LIB_A_SourceSequence13
