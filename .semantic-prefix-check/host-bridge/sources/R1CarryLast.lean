import R1InitialWalk

/-! Move the endpoint-dependent next state onto the last record of an
explicit prefix, leaving the parsed absorb fields unchanged. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.CarryLast

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

def apply (endpoint : State) : List InitialWalk.RawRec → List InitialWalk.RawRec
  | [] => []
  | [r] => [{ r with next := endpoint }]
  | r :: s :: rs => r :: apply endpoint (s :: rs)

theorem length_apply (endpoint : State) (rs : List InitialWalk.RawRec) :
    (apply endpoint rs).length = rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      cases rs with
      | nil => rfl
      | cons s rs => simp [apply, ih]

theorem apply_append_singleton (endpoint : State)
    (rs : List InitialWalk.RawRec) (r : InitialWalk.RawRec) :
    apply endpoint (rs ++ [r]) = rs ++ [{ r with next := endpoint }] := by
  induction rs with
  | nil => simp [apply]
  | cons q qs ih =>
      cases qs with
      | nil => simp [apply]
      | cons s rs =>
          simp only [List.cons_append, apply]
          change q :: apply endpoint ((s :: rs) ++ [r]) =
            q :: ((s :: rs) ++ [{ r with next := endpoint }])
          rw [ih]

theorem map_projection (endpoint : State) (rs : List InitialWalk.RawRec) :
    (apply endpoint rs).map (fun r => (r.prev, r.absorbed, r.label, r.data)) =
      rs.map (fun r => (r.prev, r.absorbed, r.label, r.data)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      cases rs with
      | nil => simp [apply]
      | cons s rs =>
          simp only [apply, List.map_cons]
          rw [ih]
          rfl

theorem records_succ (endpoint : State) (s absorbed : Nat → State)
    (label : Nat → Byte) (data : Nat → Bytes) (n : Nat) :
    apply endpoint (InitialWalk.records s absorbed label data (n + 1)) =
      InitialWalk.records s absorbed label data n ++
        [⟨s n, absorbed n, label n, data n, endpoint⟩] := by
  rw [InitialWalk.records, List.range_succ, List.map_append, List.map_singleton,
    apply_append_singleton]
  rfl

#print axioms length_apply
#print axioms apply_append_singleton
#print axioms map_projection
#print axioms records_succ

end AspisR1.CarryLast
end
