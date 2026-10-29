import Aeneas.Std
namespace PV_B3P_Length227
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem size3 {α : Type} (x0 x1 x2 : α) :
    ([x0,x1,x2] : List α).length=(3#usize).val := rfl
#print axioms size3

theorem size4 {α : Type} (x0 x1 x2 x3 : α) :
    ([x0,x1,x2,x3] : List α).length=(4#usize).val := rfl
#print axioms size4

theorem size7 {α : Type} (x0 x1 x2 x3 x4 x5 x6 : α) :
    ([x0,x1,x2,x3,x4,x5,x6] : List α).length=(7#usize).val := rfl
#print axioms size7

theorem size8 {α : Type} (x0 x1 x2 x3 x4 x5 x6 x7 : α) :
    ([x0,x1,x2,x3,x4,x5,x6,x7] : List α).length=(8#usize).val := rfl
#print axioms size8

theorem size10 {α : Type} (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : α) :
    ([x0,x1,x2,x3,x4,x5,x6,x7,x8,x9] : List α).length=(10#usize).val := rfl
#print axioms size10

theorem size14 {α : Type} (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : α) :
    ([x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13] : List α).length=(14#usize).val := rfl
#print axioms size14

theorem size15 {α : Type} (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : α) :
    ([x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14] : List α).length=(15#usize).val := rfl
#print axioms size15

theorem size16 {α : Type} (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : α) :
    ([x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15] : List α).length=(16#usize).val := rfl
#print axioms size16

theorem size20 {α : Type} (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : α) :
    ([x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19] : List α).length=(20#usize).val := rfl
#print axioms size20

theorem size32 {α : Type} (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : α) :
    ([x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24,x25,x26,x27,x28,x29,x30,x31] : List α).length=(32#usize).val := rfl
#print axioms size32

theorem size64 {α : Type} (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 : α) :
    ([x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24,x25,x26,x27,x28,x29,x30,x31,x32,x33,x34,x35,x36,x37,x38,x39,x40,x41,x42,x43,x44,x45,x46,x47,x48,x49,x50,x51,x52,x53,x54,x55,x56,x57,x58,x59,x60,x61,x62,x63] : List α).length=(64#usize).val := rfl
#print axioms size64

theorem size136 {α : Type} (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46 x47 x48 x49 x50 x51 x52 x53 x54 x55 x56 x57 x58 x59 x60 x61 x62 x63 x64 x65 x66 x67 x68 x69 x70 x71 x72 x73 x74 x75 x76 x77 x78 x79 x80 x81 x82 x83 x84 x85 x86 x87 x88 x89 x90 x91 x92 x93 x94 x95 x96 x97 x98 x99 x100 x101 x102 x103 x104 x105 x106 x107 x108 x109 x110 x111 x112 x113 x114 x115 x116 x117 x118 x119 x120 x121 x122 x123 x124 x125 x126 x127 x128 x129 x130 x131 x132 x133 x134 x135 : α) :
    ([x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15,x16,x17,x18,x19,x20,x21,x22,x23,x24,x25,x26,x27,x28,x29,x30,x31,x32,x33,x34,x35,x36,x37,x38,x39,x40,x41,x42,x43,x44,x45,x46,x47,x48,x49,x50,x51,x52,x53,x54,x55,x56,x57,x58,x59,x60,x61,x62,x63,x64,x65,x66,x67,x68,x69,x70,x71,x72,x73,x74,x75,x76,x77,x78,x79,x80,x81,x82,x83,x84,x85,x86,x87,x88,x89,x90,x91,x92,x93,x94,x95,x96,x97,x98,x99,x100,x101,x102,x103,x104,x105,x106,x107,x108,x109,x110,x111,x112,x113,x114,x115,x116,x117,x118,x119,x120,x121,x122,x123,x124,x125,x126,x127,x128,x129,x130,x131,x132,x133,x134,x135] : List α).length=(136#usize).val := rfl
#print axioms size136

end PV_B3P_Length227
