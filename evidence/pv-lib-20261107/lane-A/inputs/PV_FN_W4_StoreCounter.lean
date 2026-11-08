import PV_FN_W4_OwnChain
set_option autoImplicit false
namespace PV_FN_W4_StoreCounter
open PV_STX2_Syntax PV_STX2_Store

/-- Store binding and operand moves never allocate activations. The native
call-entry supply must be incremented only by its actual call instruction. -/
theorem writeAddressCounter {W V : Type} (C : Carrier W V) (s t : Store V)
    (p : Address) (value : Option V) (h : writeAddress C s p value = some t) :
    t.nextActivation = s.nextActivation := by
  cases fields : p.fields with
  | nil => simp only [writeAddress,fields] at h; cases h; rfl
  | cons n ns =>
    cases root : s.cells {p with fields := []} with
    | none => simp [writeAddress,fields,root] at h
    | some v =>
      cases changed : replaceFields C (n :: ns) value v with
      | none => simp [writeAddress,fields,root,changed] at h
      | some v' => simp [writeAddress,fields,root,changed] at h; cases h; rfl

theorem operandCounter {W V : Type} (C : Carrier W V) (s t : Store V)
    (w : W) (a : Nat) (o : Operand) (v : V) (h : operand C s w a o = some (v,t)) :
    t.nextActivation = s.nextActivation := by
  cases o with
  | constant d => cases val : C.constant d <;> simp [operand,val] at h; obtain ⟨rfl,rfl⟩ := h; rfl
  | copy p => cases val : read C s w a p <;> simp [operand,val] at h; obtain ⟨rfl,rfl⟩ := h; rfl
  | move p =>
    cases val : read C s w a p with
    | none => simp [operand,val] at h
    | some v' =>
      cases loc : locate C s w a p with
      | none => simp [operand,val,loc] at h
      | some addr =>
        cases upd : writeAddress C s addr none with
        | none => simp [operand,val,loc,upd] at h
        | some u =>
          simp [operand,val,loc,upd] at h
          obtain ⟨rfl,rfl⟩ := h
          exact writeAddressCounter C s _ addr none upd

theorem operandsCounter {W V : Type} (C : Carrier W V) (s t : Store V)
    (w : W) (a : Nat) (os : List Operand) (vs : List V)
    (h : operands C w a os s = some (vs,t)) : t.nextActivation = s.nextActivation := by
  induction os generalizing s vs with
  | nil => simp [operands] at h; obtain ⟨rfl,rfl⟩ := h; rfl
  | cons o os ih =>
    cases first : operand C s w a o with
    | none => simp [operands,first] at h
    | some pair =>
      rcases pair with ⟨v,u⟩
      cases rest : operands C w a os u with
      | none => simp [operands,first,rest] at h
      | some pair =>
        rcases pair with ⟨values,z⟩
        simp [operands,first,rest] at h
        obtain ⟨rfl,rfl⟩ := h
        exact (ih u values rest).trans (operandCounter C s u w a o v first)

/-- Symbolic induction covers every expression shape; no generated numeral or
recurrence is normalized. Operator/native values remain arbitrary. -/
theorem evaluateCounter {W V : Type} (C : Carrier W V) (s t : Store V)
    (w : W) (a : Nat) (e : Expr) (v : V) (h : evaluate C s w a e = some (v,t)) :
    t.nextActivation = s.nextActivation := by
  cases e with
  | use o => exact operandCounter C s _ w a o v h
  | reference p metadata =>
    cases loc : locate C s w a p with
    | none => simp [evaluate,loc] at h
    | some addr =>
      cases val : operand C s w a metadata with
      | none => simp [evaluate,loc,val] at h
      | some pair =>
        rcases pair with ⟨m,u⟩
        simp [evaluate,loc,val] at h
        obtain ⟨_,rfl⟩ := h
        exact operandCounter C s _ w a metadata m val
  | rawPointer p metadata =>
    cases loc : locate C s w a p with
    | none => simp [evaluate,loc] at h
    | some addr =>
      cases val : operand C s w a metadata with
      | none => simp [evaluate,loc,val] at h
      | some pair =>
        rcases pair with ⟨m,u⟩
        simp [evaluate,loc,val] at h
        obtain ⟨_,rfl⟩ := h
        exact operandCounter C s _ w a metadata m val
  | aggregate kind os =>
    cases args : operands C w a os s with
    | none => simp [evaluate,args] at h
    | some pair =>
      rcases pair with ⟨values,u⟩
      cases val : C.aggregate kind values with
      | none => simp [evaluate,args,val] at h
      | some value =>
        simp [evaluate,args,val] at h
        obtain ⟨rfl,rfl⟩ := h
        exact operandsCounter C s _ w a os values args
  | unary op o =>
    cases arg : operand C s w a o with
    | none => simp [evaluate,arg] at h
    | some pair =>
      rcases pair with ⟨value,u⟩
      cases val : C.unary op value with
      | none => simp [evaluate,arg,val] at h
      | some value' =>
        simp [evaluate,arg,val] at h
        obtain ⟨rfl,rfl⟩ := h
        exact operandCounter C s _ w a o value arg
  | binary op l r =>
    cases left : operand C s w a l with
    | none => simp [evaluate,left] at h
    | some pair =>
      rcases pair with ⟨lv,u⟩
      cases right : operand C u w a r with
      | none => simp [evaluate,left,right] at h
      | some pair =>
        rcases pair with ⟨rv,z⟩
        cases val : C.binary op lv rv with
        | none => simp [evaluate,left,right,val] at h
        | some value =>
          simp [evaluate,left,right,val] at h
          obtain ⟨rfl,rfl⟩ := h
          exact (operandCounter C u _ w a r rv right).trans (operandCounter C s u w a l lv left)
  | nullary op => cases val : C.nullary w op <;> simp [evaluate,val] at h; obtain ⟨rfl,rfl⟩ := h; rfl

theorem bindCounter {W V : Type} (C : Carrier W V) (s t : Store V)
    (w : W) (a : Nat) (dest : Place) (e : Expr) (h : PV_STX2_Store.bind C s w a dest e = some t) :
    t.nextActivation = s.nextActivation := by
  cases val : evaluate C s w a e with
  | none => simp [PV_STX2_Store.bind,val] at h
  | some pair =>
    rcases pair with ⟨value,u⟩
    cases loc : locate C u w a dest with
    | none => simp [PV_STX2_Store.bind,val,loc] at h
    | some addr =>
      simp [PV_STX2_Store.bind,val,loc] at h
      exact (writeAddressCounter C u _ addr (some value) h).trans (evaluateCounter C s u w a e value val)

#print axioms writeAddressCounter
#print axioms operandCounter
#print axioms operandsCounter
#print axioms evaluateCounter
#print axioms bindCounter
end PV_FN_W4_StoreCounter
