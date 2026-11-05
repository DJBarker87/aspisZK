import NHT_TailView
set_option autoImplicit false
namespace NHV_WindowFrame
/-- A native cut that reads only this exact window is independent of all bytes
outside it. This is a list-value frame law, not a physical-memory certificate. -/
theorem window_frame {α : Type} (before after : List α) (lo width : Nat)
 (same : (before.drop lo).take width=(after.drop lo).take width) :
 ∀ i, i<width → ((before.drop lo).take width)[i]?=((after.drop lo).take width)[i]? := by
 intro i hi
 rw [same]

/-- Exact adjacent source windows concatenate without dropping or duplicating a
byte; this supplies the value frame used when native cuts are one window wide. -/
theorem adjacent {α : Type} (proof : List α) (lo first second : Nat) :
 (proof.drop lo).take first ++ (proof.drop (lo+first)).take second =
 (proof.drop lo).take (first+second) := by
 rw [← List.drop_drop]
 exact List.take_add.symm

/-- Length is derived from the original proof length and checked endpoints,
not assumed separately at each consumer. -/
theorem width {α : Type} (proof : List α) (lo width : Nat)
 (bound : lo+width≤proof.length) : ((proof.drop lo).take width).length=width := by
 rw [List.length_take,List.length_drop]
 apply Nat.min_eq_left
 omega
#print axioms window_frame
#print axioms adjacent
#print axioms width
end NHV_WindowFrame
