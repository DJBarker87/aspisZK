import NIS_SdkCopyCanonical
set_option autoImplicit false
namespace NIJ_SdkCopyFields
open AspisR1.S2Trust

theorem guards {F : Type} (s : Heap F) (g : Guard) (source : Nat → UInt8) (start n : Nat) :
 (NIJ_SdkWriteLoop.copy s g source start n).guards=s.guards := by
 have h:=NIJ_SdkCopyCanonical.unchanged s g source start n
 have projected:=congrArg (fun x : Heap F => x.guards) h
 exact projected

theorem counter {F : Type} (s : Heap F) (g : Guard) (source : Nat → UInt8) (start n : Nat) :
 (NIJ_SdkWriteLoop.copy s g source start n).counter=s.counter := by
 have projected:=congrArg (fun x : Heap F => x.counter) (NIJ_SdkCopyCanonical.unchanged s g source start n)
 exact projected

theorem lookup {F : Type} (s : Heap F) (g : Guard) (source : Nat → UInt8) (start n token : Nat) :
 AspisR1.S2Trust.lookup (NIJ_SdkWriteLoop.copy s g source start n) token=AspisR1.S2Trust.lookup s token := by
 unfold AspisR1.S2Trust.lookup
 rw [guards]

theorem ambient {F : Type} (s : Heap F) (g : Guard) (source : Nat → UInt8) (start n : Nat) :
 (NIJ_SdkWriteLoop.copy s g source start n).ambient=s.ambient := by
 have projected:=congrArg (fun x : Heap F => x.ambient) (NIJ_SdkCopyCanonical.unchanged s g source start n)
 exact projected

#print axioms guards
#print axioms counter
#print axioms lookup
#print axioms ambient
end NIJ_SdkCopyFields
