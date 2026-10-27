import R1Z.PV_Inv_TaggedBank
set_option autoImplicit false
namespace R1Z.PV_Inv_RegistryInput
open R0P PV_Inv_BankSource PV_Inv_BankPattern
variable {K : Type} [Field K]

structure SourceLink (K : Type) where
  tag : Nat
  weightKind : Fin 5
  weightLevel : Nat
  producer : Tuple K
  consumer : Tuple K

def ofModel (l : CopyLink) : SourceLink K :=
  ⟨l.tag,l.weightKind,l.weightLevel,descriptor l.producer,descriptor l.consumer⟩

/-- OPEN P_registry at pair_forest_trace.rs:545–599. The installed call must
return these descriptors in this order. A static terminal-table identity alone
is insufficient: the native enumerator calls the schedule and legacy registry. -/
def P_registry (native : List (SourceLink K)) : Prop :=
  native = copyLinks.map ofModel

/-- OPEN P_banks at pair_forest_trace.rs:601–614 and host_semantic.rs:241.
The selected bank cells must be this very headline build trace, including the
caller mask application; no arbitrary trace may be substituted. -/
def P_banks (native : Banks K) (headlineTrace : Trace K) : Prop :=
  BankJoin native headlineTrace

theorem member (native : List (SourceLink K)) (h : P_registry native)
    (l : SourceLink K) (hl : l ∈ native) :
    ∃ model ∈ copyLinks, ofModel model = l := by
  rw [h] at hl
  exact List.mem_map.mp hl

#print axioms member
end R1Z.PV_Inv_RegistryInput
