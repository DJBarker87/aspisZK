import Port4B_SlotInstall
set_option autoImplicit false
namespace AspisR1.JGh_TX2_SlotOffsets

theorem off3 : (Port4B_SlotInstall.offset 3 (by decide)).val=41799 := rfl
#print axioms off3
theorem off4 : (Port4B_SlotInstall.offset 4 (by decide)).val=47303 := rfl
#print axioms off4
theorem off5 : (Port4B_SlotInstall.offset 5 (by decide)).val=52807 := rfl
#print axioms off5
theorem off6 : (Port4B_SlotInstall.offset 6 (by decide)).val=57607 := rfl
#print axioms off6
end AspisR1.JGh_TX2_SlotOffsets
