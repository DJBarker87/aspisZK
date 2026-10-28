import R1Z.PV_W_TypedEffects
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_W_ReachedEffects
open ProverRwFull PV_W_Syntax PV_W_SyntaxMap
open Aeneas Aeneas.Std
variable [ExternalTypes]

/-- Reached operations retain their values and generic type. Metadata is
resolved in the current interpreter world, never guessed from the Vec list. -/
inductive Op : Type → Type 1 where
  | base {A : Type} (op : PV_W_TypedEffects.Primitive A) : Op A
  | reserve {T : Type} (Allocator : Type) (v : alloc.vec.Vec T) (n : Usize) :
      Op ((core.result.Result Unit alloc.collections.TryReserveError) × alloc.vec.Vec T)
  | dropWords (v : alloc.vec.Vec U32) : Op Unit
  | zeroArray (N : Usize) (a : Array U8 N) : Op (Array U8 N)
  | zeroByte (a : U8) : Op U8

def embed {A : Type} : Op A → PV_W_SourceSyntax.Op A
  | .base op => PV_W_TypedEffects.embed op
  | .reserve Allocator v n => ⟨"alloc.vec.Vec.try_reserve_exact",fun dictionary =>
      @alloc.vec.Vec.try_reserve_exact _ dictionary _ Allocator v n⟩
  | .dropWords v => ⟨"core.mem.drop",fun dictionary => @core.mem.drop _ dictionary _ v⟩
  | .zeroArray N a => ⟨"Array.Insts.ZeroizeZeroize.zeroize",fun dictionary =>
      (@Array.Insts.ZeroizeZeroize _ dictionary U8 N
        (@zeroize.Zeroize.Blanket _ dictionary U8 U8.Insts.ZeroizeDefaultIsZeroes)).zeroize a⟩
  | .zeroByte a => ⟨"zeroize.Zeroize.Blanket.zeroize",fun dictionary =>
      (@zeroize.Zeroize.Blanket _ dictionary U8 U8.Insts.ZeroizeDefaultIsZeroes).zeroize a⟩

abbrev P (A : Type) := Program Op Aeneas.Std.Error A
instance : Monad P where
  pure := Program.pure
  bind := thenDo

def perform {A : Type} (op : Op A) : P A := .call op .pure

def invoke {A : Type} (label : String)
    (f : ExternalFuns → Aeneas.Std.Result A) : P A := perform (.base (.helper ⟨label,f⟩))

def erase {A : Type} (dictionary : ExternalFuns) (p : P A) : Aeneas.Std.Result A :=
  PV_W_SourceSyntax.erase dictionary (mapOps embed p)

theorem erase_bind {A B : Type} (dictionary : ExternalFuns)
    (p : P A) (k : A → P B) :
    erase dictionary (p >>= k) = Aeneas.Std.bind (erase dictionary p) (fun a => erase dictionary (k a)) := by
  change PV_W_SourceSyntax.erase dictionary (mapOps embed (thenDo p k)) = _
  rw [map_bind,PV_W_SourceSyntax.erase_thenDo]
  rfl

theorem erase_perform {A : Type} (dictionary : ExternalFuns) (op : Op A) :
    erase dictionary (perform op) = (embed op).source dictionary := by
  change PV_W_SourceSyntax.erase dictionary
    (PV_W_SourceSyntax.invoke (embed op).label (embed op).source) = _
  exact PV_W_SourceSyntax.erase_invoke dictionary _ _

theorem erase_invoke {A : Type} (dictionary : ExternalFuns) (label : String)
    (f : ExternalFuns → Aeneas.Std.Result A) : erase dictionary (invoke label f) = f dictionary :=
  erase_perform dictionary (.base (.helper ⟨label,f⟩))

theorem erase_pure {A : Type} (dictionary : ExternalFuns) (a : A) :
    erase dictionary (pure a : P A) = .ok a := rfl

#print axioms erase_bind
#print axioms erase_perform
#print axioms erase_invoke
#print axioms erase_pure
end R1Z.PV_W_ReachedEffects
