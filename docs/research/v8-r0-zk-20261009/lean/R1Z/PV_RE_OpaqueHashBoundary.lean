import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_OpaqueHashBoundary
open Aeneas.Std ProverRwFull
variable [ExternalTypes]
abbrev Digest := Array U8 32#usize
abbrev Hash := Slice (Slice U8) → Result Digest
/-- A legal implementation of the actual op84 interface, demonstrating that
this opaque interface itself does not require forwarding. Not a native law. -/
@[reducible] def catch84 (D : ExternalFuns) (parts : Slice (Slice U8)) (fallback : Digest) : ExternalFuns :=
  {D with op84 := fun hash _ _ =>
    match hash parts with
    | .ok value => Result.ok value
    | .fail _ => Result.ok fallback
    | .div => Result.ok fallback}

theorem op84_can_catch (D : ExternalFuns) (parts : Slice (Slice U8))
    (fallback : Digest) (hash : Hash) (tag : U8) (values : Slice U8)
    (e : Error) (h : hash parts = .fail e) :
    @aspis_core.r0.merkle.leaf _ (catch84 D parts fallback) hash tag values =
      .ok fallback := by
  change (match hash parts with
    | .ok value => Result.ok value
    | .fail _ => Result.ok fallback
    | .div => Result.ok fallback) = Result.ok fallback
  rw [h]

/-- The same concrete higher-order boundary can suppress divergence. -/
theorem op84_can_suppress_divergence (D : ExternalFuns) (parts : Slice (Slice U8))
    (fallback : Digest) (hash : Hash) (tag : U8) (values : Slice U8)
    (h : hash parts = .div) :
    @aspis_core.r0.merkle.leaf _ (catch84 D parts fallback) hash tag values =
      .ok fallback := by
  change (match hash parts with
    | .ok value => Result.ok value
    | .fail _ => Result.ok fallback
    | .div => Result.ok fallback) = Result.ok fallback
  rw [h]

#print axioms catch84
#print axioms op84_can_catch
#print axioms op84_can_suppress_divergence
end R1Z.PV_RE_OpaqueHashBoundary
