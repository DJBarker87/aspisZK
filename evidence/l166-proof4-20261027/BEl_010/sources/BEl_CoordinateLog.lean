import BEl_FullLog
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_CoordinateLog
open BEl_FullLog

def lengths {Byte Reply : Type} (log : List (Record Byte Reply)) (i : Nat) :=
  log[i]?.map (fun r => r.input.map List.length)

def byte {Byte Reply : Type} (log : List (Record Byte Reply)) (i p j : Nat) :=
  log[i]?.bind (fun r => r.input[p]?.bind (fun part => part[j]?))

def reply {Byte Reply : Type} (log : List (Record Byte Reply)) (i : Nat) :=
  log[i]?.map Record.returned

/-- The universal projections used by the split Rust observer determine
complete chronological occurrence lists, including repeated addresses. -/
theorem ext {Byte Reply : Type} (left right : List (Record Byte Reply))
    (sizes : ∀ i, lengths left i = lengths right i)
    (bytes : ∀ i p j, byte left i p j = byte right i p j)
    (returned : ∀ i, reply left i = reply right i) : left = right := by
  apply List.ext_getElem?
  intro i
  have present := sizes i
  cases a : left[i]? with
  | none =>
    cases b : right[i]? with
    | none => rfl
    | some y => simp only [lengths,a,b,Option.map_none,Option.map_some] at present; cases present
  | some x =>
    cases b : right[i]? with
    | none => simp only [lengths,a,b,Option.map_none,Option.map_some] at present; cases present
    | some y =>
      congr 1
      apply record_ext x y
      · exact Option.some.inj (by simpa only [lengths,a,b,Option.map_some] using present)
      · intro p j
        simpa only [byte,a,b,Option.bind_some] using bytes i p j
      · exact Option.some.inj (by simpa only [reply,a,b,Option.map_some] using returned i)

/-- Oracle addresses are concatenated inputs. Equal part records imply
address equality as a derived fact; no separate hash of the address is used. -/
theorem addresses {Byte Reply : Type} (left right : List (Record Byte Reply))
    (sizes : ∀ i, lengths left i = lengths right i)
    (bytes : ∀ i p j, byte left i p j = byte right i p j)
    (returned : ∀ i, reply left i = reply right i) :
    left.map (fun r => r.input.flatten) = right.map (fun r => r.input.flatten) := by
  rw [ext left right sizes bytes returned]

#print axioms ext
#print axioms addresses
end AspisR1.BEl_CoordinateLog
end
