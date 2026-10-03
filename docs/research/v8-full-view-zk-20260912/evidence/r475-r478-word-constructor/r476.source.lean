import AspisV8R19.R475PointerWordRuntime

/-! Word-valued execution for the complete checked constructor fragment.
This is a BitVec/Nat model correspondence only; it does not establish Rust
source semantics or caller validity. -/
set_option autoImplicit false
namespace AspisV8R19.R476WordConstructorExecution
open AspisV8R19.R432PointerPrimitive
open AspisV8R19.R433ConstructorFragment
open AspisV8R19.R475PointerWordRuntime

abbrev WordLocals := Nat → Option WordValue

def put (locals : WordLocals) (index : Nat) (value : Option WordValue) : WordLocals :=
  fun other => if other = index then value else locals other

def decodeLocals (locals : WordLocals) : Locals :=
  fun i => (locals i).map decode

inductive WordControl where
  | cont (locals : WordLocals)
  | returned (value : WordValue) (locals : WordLocals)

def decodeControl : WordControl → Control
  | .cont locals => .cont (decodeLocals locals)
  | .returned value locals => .returned (decode value) (decodeLocals locals)

 theorem put_decode (locals : WordLocals) (index : Nat)
    (value : Option WordValue) :
    decodeLocals (put locals index value) =
      R433ConstructorFragment.put (decodeLocals locals) index (value.map decode) := by
  funext other
  by_cases h : other = index <;> simp [decodeLocals, put, R433ConstructorFragment.put, h]

 def wordLengthEq (left right : BitVec 64) : Prop := left.toNat = right.toNat

theorem word_length_eq_iff (left right : BitVec 64) :
    (left = right) ↔ wordLengthEq left right := by
  constructor
  · intro h
    simpa [wordLengthEq, h]
  · intro h
    apply BitVec.eq_of_toNat_eq
    exact h

def command {T : Type} (heap : Heap T) (locals : WordLocals) :
    Command → Option WordControl
  | .live index => some (.cont (put locals index none))
  | .dead index => some (.cont (put locals index none))
  | .metadata dst src => do
      let .sliceRef _ length ← locals src | none
      some (.cont (put locals dst (some (.word length))))
  | .rawSlice dst src metadataSource => do
      let .sliceRef ptr length ← locals src | none
      let .sliceRef _ metadataLength ← locals metadataSource | none
      if length.toNat = metadataLength.toNat then
        some (.cont (put locals dst (some (.rawFat .shared ptr length))))
      else none
  | .cast dst src kind => do
      let value ← locals src
      let result ← checkedCast kind value
      some (.cont (put locals dst (some result)))
  | .offset dst pointerSource countSource => do
      let .rawThin .mut ptr ← locals pointerSource | none
      let .word count ← locals countSource | none
      let ptr1 ← offset heap ptr count
      some (.cont (put locals dst (some (.rawThin .mut ptr1))))
  | .marker dst => some (.cont (put locals dst (some .marker)))
  | .iterator dst pointerSource endSource markerSource => do
      let .nonNullThin ptr ← locals pointerSource | none
      let .rawThin .shared last ← locals endSource | none
      let .marker ← locals markerSource | none
      let locals1 := put locals markerSource none
      some (.cont (put locals1 dst (some (.iterator ⟨ptr, last⟩))))
  | .ret => do
      let value ← locals 0
      some (.returned value locals)

def program {T : Type} (heap : Heap T) (locals : WordLocals) :
    Program → Option WordControl
  | .nop => some (.cont locals)
  | .one operation => command heap locals operation
  | .seq first second => do
      match ← program heap locals first with
      | .cont locals1 => program heap locals1 second
      | .returned value locals1 => some (.returned value locals1)
  | .globalIf id ifTrue ifFalse => do
      let .bool value ←
        AspisV8R19.R470R440ReadonlyConstantGraph.eval 7 (.global id) | none
      if value then program heap locals ifTrue
      else program heap locals ifFalse

attribute [simp] decodeControl decode put_decode

theorem command_decode {T : Type} (heap : Heap T) (locals : WordLocals)
    (op : Command) :
    (command heap locals op).map decodeControl =
      R472CheckedConstructor.command heap (decodeLocals locals) op := by
  cases op with
  | live index => simp [command, R472CheckedConstructor.command, evalCommand, put_decode]
  | dead index => simp [command, R472CheckedConstructor.command, evalCommand, put_decode]
  | metadata dst src =>
      cases h : locals src with
      | none => simp [command, R472CheckedConstructor.command, evalCommand, decodeLocals, h]
      | some value =>
        cases value <;> simp [command, R472CheckedConstructor.command, evalCommand,
          decodeLocals, h, put_decode]
  | rawSlice dst src metadataSource =>
      cases hs : locals src with
      | none => simp [command, R472CheckedConstructor.command, evalCommand, decodeLocals, hs]
      | some source =>
        cases source with
        | sliceRef ptr length =>
          cases hm : locals metadataSource with
          | none => simp [command, R472CheckedConstructor.command, evalCommand, decodeLocals, hs, hm]
          | some metadata =>
            cases metadata <;> simp [command, R472CheckedConstructor.command, evalCommand,
              decodeLocals, hs, hm, word_length_eq_iff, put_decode]
        | _ => simp [command, R472CheckedConstructor.command, evalCommand, decodeLocals, hs]
  | cast dst src kind =>
      cases hs : locals src with
      | none => simp [command, R472CheckedConstructor.command, evalCommand, decodeLocals, hs]
      | some value =>
        have hh := checked_cast_decode kind value
        cases hr : checkedCast kind value <;>
          simp [hr] at hh <;>
          simp [command, R472CheckedConstructor.command, decodeLocals, hs, hr, ← hh]
  | offset dst pointerSource countSource =>
      cases hp : locals pointerSource with
      | none => simp [command, R472CheckedConstructor.command, evalCommand, decodeLocals, hp]
      | some p =>
        cases p with
        | rawThin mutability ptr =>
          cases mutability <;> cases hc : locals countSource with
          | none => simp [command, R472CheckedConstructor.command, evalCommand, decodeLocals, hp, hc]
          | some c =>
            cases c <;> simp [command, R472CheckedConstructor.command, evalCommand,
              decodeLocals, hp, hc, put_decode]
            all_goals
              rename_i count
              rw [← offset_decode heap ptr count]
              cases offset heap ptr count <;> rfl
        | _ => simp [command, R472CheckedConstructor.command, evalCommand, decodeLocals, hp]
  | marker dst => simp [command, R472CheckedConstructor.command, evalCommand, put_decode]
  | iterator dst pointerSource endSource markerSource =>
      cases hp : locals pointerSource with
      | none => simp [command, R472CheckedConstructor.command, evalCommand, decodeLocals, hp]
      | some p =>
        cases p with
        | nonNullThin ptr =>
          cases he : locals endSource with
          | none => simp [command, R472CheckedConstructor.command, evalCommand, decodeLocals, hp, he]
          | some e =>
            cases e with
            | rawThin mutability last =>
              cases mutability <;> cases hm : locals markerSource with
              | none => simp [command, R472CheckedConstructor.command, evalCommand, decodeLocals, hp, he, hm]
              | some m =>
                cases m <;> simp [command, R472CheckedConstructor.command, evalCommand,
                  decodeLocals, hp, he, hm, put_decode]
            | _ => simp [command, R472CheckedConstructor.command, evalCommand, decodeLocals, hp, he]
        | _ => simp [command, R472CheckedConstructor.command, evalCommand, decodeLocals, hp]
  | ret =>
      cases h : locals 0 with
      | none => simp [command, R472CheckedConstructor.command, evalCommand, decodeLocals, h]
      | some value => simp [command, R472CheckedConstructor.command, evalCommand, decodeLocals, h]

theorem program_decode {T : Type} (heap : Heap T) (locals : WordLocals)
    (code : Program) :
    (program heap locals code).map decodeControl =
      R472CheckedConstructor.program heap (decodeLocals locals) code := by
  induction code generalizing locals with
  | nop => simp [program, R472CheckedConstructor.program, decodeControl]
  | one op => exact command_decode heap locals op
  | seq first second ihFirst ihSecond =>
      have hh := ihFirst locals
      cases hr : program heap locals first with
      | none =>
          simp [hr] at hh
          simp [program, R472CheckedConstructor.program, hr, ← hh]
      | some result =>
          cases result <;> simp [hr] at hh <;>
            simp [program, R472CheckedConstructor.program, hr, ← hh, ihSecond]
  | globalIf id ifTrue ifFalse ihTrue ihFalse =>
      cases hg : AspisV8R19.R470R440ReadonlyConstantGraph.eval 7 (.global id) with
      | none => simp [program, R472CheckedConstructor.program, hg]
      | some value =>
          cases value <;> simp [program, R472CheckedConstructor.program, hg, ihTrue, ihFalse]
          split <;> simp_all

#print axioms command_decode
#print axioms program_decode
end AspisV8R19.R476WordConstructorExecution
