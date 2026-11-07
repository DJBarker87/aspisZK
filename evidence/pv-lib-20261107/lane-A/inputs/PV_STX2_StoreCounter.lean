import PV_STX2_SliceMachine
set_option autoImplicit false
namespace PV_STX2_StoreCounter
open PV_STX2_Syntax PV_STX2_Store
variable {W V : Type}
/-- Conditional on owner acceptance of the translator patch. Store operations
retain the unused activation counter; only call issuance increments it. -/
theorem writeAddress (c : Carrier W V) (s t : Store V) (p : Address) (v : Option V)
    (h : PV_STX2_Store.writeAddress c s p v = some t) : t.nextActivation = s.nextActivation := by
  unfold PV_STX2_Store.writeAddress at h
  split at h
  · cases h; rfl
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def] at h
    rcases h with ⟨root,_,changed,_,e⟩
    cases e; rfl

/-- Conditional on owner acceptance of the translator patch. Store operations
retain the unused activation counter; only call issuance increments it. -/
theorem operand (c : Carrier W V) (s t : Store V) (w : W) (a : Nat) (o : Operand) (v : V)
    (h : PV_STX2_Store.operand c s w a o = some (v,t)) : t.nextActivation = s.nextActivation := by
  cases o <;> simp only [PV_STX2_Store.operand, Option.map_eq_some_iff] at h
  all_goals first
    | rcases h with ⟨x,h,e⟩; cases e; rfl
    | skip
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  rcases h with ⟨x,_,p,_,u,hu,e⟩
  cases e
  exact writeAddress c s t p none hu

/-- Conditional on owner acceptance of the translator patch. Store operations
retain the unused activation counter; only call issuance increments it. -/
theorem operands (c : Carrier W V) (s t : Store V) (w : W) (a : Nat) (os : List Operand) (vs : List V)
    (h : PV_STX2_Store.operands c w a os s = some (vs,t)) : t.nextActivation = s.nextActivation := by
  induction os generalizing s vs with
  | nil => cases h; rfl
  | cons o os ih =>
    simp only [PV_STX2_Store.operands, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    rcases h with ⟨⟨v,u⟩,ho,⟨values,z⟩,hos,e⟩
    cases e
    exact (ih u values hos).trans (operand c s u w a o v ho)

/-- Conditional on owner acceptance of the translator patch. Store operations
retain the unused activation counter; only call issuance increments it. -/
theorem evaluate (c : Carrier W V) (s t : Store V) (w : W) (a : Nat) (e : Expr) (v : V)
    (h : PV_STX2_Store.evaluate c s w a e = some (v,t)) : t.nextActivation = s.nextActivation := by
  cases e with
  | use o => exact operand c s t w a o v h
  | nullary op =>
    simp only [PV_STX2_Store.evaluate,Option.map_eq_some_iff] at h
    rcases h with ⟨x,_,e⟩; cases e; rfl
  | reference p metadata | rawPointer p metadata =>
    simp only [PV_STX2_Store.evaluate,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def] at h
    rcases h with ⟨addr,_,⟨m,u⟩,ho,e⟩; cases e
    exact operand c s _ w a metadata m ho
  | aggregate tag os =>
    simp only [PV_STX2_Store.evaluate,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def] at h
    rcases h with ⟨⟨vs,u⟩,ho,x,_,e⟩; cases e
    exact operands c s _ w a os vs ho
  | unary op o =>
    simp only [PV_STX2_Store.evaluate,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def] at h
    rcases h with ⟨⟨x,u⟩,ho,y,_,e⟩; cases e
    exact operand c s _ w a o x ho
  | binary op l r =>
    simp only [PV_STX2_Store.evaluate,Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def] at h
    rcases h with ⟨⟨x,u⟩,hl,⟨y,z⟩,hr,b,_,e⟩; cases e
    exact (operand c u _ w a r y hr).trans (operand c s u w a l x hl)

/-- Conditional on owner acceptance of the translator patch. Store operations
retain the unused activation counter; only call issuance increments it. -/
theorem bind (c : Carrier W V) (s t : Store V) (w : W) (a : Nat) (p : Place) (e : Expr)
    (h : PV_STX2_Store.bind c s w a p e = some t) : t.nextActivation = s.nextActivation := by
  simp only [PV_STX2_Store.bind,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
  rcases h with ⟨⟨v,u⟩,he,addr,_,hw⟩
  exact (writeAddress c u t addr (some v) hw).trans (evaluate c s u w a e v he)

/-- Conditional on owner acceptance of the translator patch. Store operations
retain the unused activation counter; only call issuance increments it. -/
theorem arguments (a : Nat) (vs : List V) (n : Nat) (s : Store V) :
    (PV_STX2_Native.arguments a vs n s).nextActivation = s.nextActivation := by
  induction vs generalizing n s with
  | nil => rfl
  | cons v vs ih => exact ih (n+1) (write s ⟨a,n,[]⟩ (some v))
#print axioms writeAddress
#print axioms operand
#print axioms operands
#print axioms evaluate
#print axioms bind
#print axioms arguments
end PV_STX2_StoreCounter
