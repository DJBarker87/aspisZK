import PV_FN_THREAD_f361NameEntryValidity
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_NameValidity
open PV_STX2_Syntax PV_EVHB_OwnerMachine PV_FN_THREAD_f361
open PV_THR2_LibrarySemantics_ThreadNew213
/-- The actual None source constructor needs no String buffer interpretation.
The Some case stays separate with its real ownership/word-validity obligation. -/
theorem none_entry (R : Representation) (x : Input) (descriptor metadata : Data)
    (labelEq : x.threadName = PV_THR2_KeyValues.pack
      (.object [("Adt",.array [descriptor,.number 0,metadata])]) []) :
    PV_FN_THREAD_f361NameEntryValidity.EntryName R x := by
  refine ⟨none,?_,?_⟩
  · rw [labelEq]
    exact .none descriptor metadata
  · intro b impossible
    cases impossible

/-- Source-provenance form of the Some branch: opaque String decoding and
buffer ownership are the provider's own definitions. No read at a later call,
Scope separation, native success or invented field layout occurs in it. -/
theorem some_entry (R : Representation) (x : Input) (descriptor metadata value : Data)
    (buffer : Buffer)
    (labelEq : x.threadName = PV_THR2_KeyValues.pack
      (.object [("Adt",.array [descriptor,.number 1,metadata])]) [value])
    (decode : R.decode value = some buffer) (owned : Owned x.w buffer)
    (word : buffer.pointer < 2^64) :
    PV_FN_THREAD_f361NameEntryValidity.EntryName R x := by
  refine ⟨some buffer,?_,?_⟩
  · rw [labelEq]
    exact .some descriptor metadata value buffer decode owned
  · intro b same
    cases same
    exact word
#print axioms none_entry
#print axioms some_entry
end PV_LIB_A_NameValidity
