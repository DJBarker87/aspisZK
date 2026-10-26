import R1Z.PDict_CodecDictionary
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_CurrentRetention
open Aeneas Aeneas.Std ProverRwFull
open PDict_CodecDictionary (native selected)

theorem retain_0 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op0 (native base) (selected base ops) =
    @ExternalFuns.op0 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_0

theorem retain_1 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op1 (native base) (selected base ops) =
    @ExternalFuns.op1 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_1

theorem retain_2 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op2 (native base) (selected base ops) =
    @ExternalFuns.op2 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_2

theorem retain_3 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op3 (native base) (selected base ops) =
    @ExternalFuns.op3 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_3

theorem retain_4 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op4 (native base) (selected base ops) =
    @ExternalFuns.op4 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_4

theorem retain_5 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op5 (native base) (selected base ops) =
    @ExternalFuns.op5 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_5

theorem retain_6 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op6 (native base) (selected base ops) =
    @ExternalFuns.op6 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_6

theorem retain_7 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op7 (native base) (selected base ops) =
    @ExternalFuns.op7 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_7

theorem retain_8 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op8 (native base) (selected base ops) =
    @ExternalFuns.op8 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_8

theorem retain_9 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op9 (native base) (selected base ops) =
    @ExternalFuns.op9 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_9

theorem retain_10 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op10 (native base) (selected base ops) =
    @ExternalFuns.op10 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_10

theorem retain_11 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op11 (native base) (selected base ops) =
    @ExternalFuns.op11 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_11

theorem retain_12 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op12 (native base) (selected base ops) =
    @ExternalFuns.op12 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_12

theorem retain_13 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op13 (native base) (selected base ops) =
    @ExternalFuns.op13 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_13

theorem retain_14 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op14 (native base) (selected base ops) =
    @ExternalFuns.op14 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_14

theorem retain_15 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op15 (native base) (selected base ops) =
    @ExternalFuns.op15 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_15

theorem retain_16 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op16 (native base) (selected base ops) =
    @ExternalFuns.op16 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_16

theorem retain_17 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op17 (native base) (selected base ops) =
    @ExternalFuns.op17 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_17

theorem retain_18 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op18 (native base) (selected base ops) =
    @ExternalFuns.op18 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_18

theorem retain_19 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op19 (native base) (selected base ops) =
    @ExternalFuns.op19 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_19

theorem retain_20 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op20 (native base) (selected base ops) =
    @ExternalFuns.op20 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_20

theorem retain_21 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op21 (native base) (selected base ops) =
    @ExternalFuns.op21 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_21

theorem retain_22 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op22 (native base) (selected base ops) =
    @ExternalFuns.op22 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_22

theorem retain_23 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op23 (native base) (selected base ops) =
    @ExternalFuns.op23 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_23

theorem retain_24 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op24 (native base) (selected base ops) =
    @ExternalFuns.op24 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_24

theorem retain_25 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op25 (native base) (selected base ops) =
    @ExternalFuns.op25 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_25

theorem retain_26 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op26 (native base) (selected base ops) =
    @ExternalFuns.op26 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_26

theorem retain_27 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op27 (native base) (selected base ops) =
    @ExternalFuns.op27 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_27

theorem retain_28 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op28 (native base) (selected base ops) =
    @ExternalFuns.op28 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_28

theorem retain_29 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op29 (native base) (selected base ops) =
    @ExternalFuns.op29 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_29

theorem retain_30 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op30 (native base) (selected base ops) =
    @ExternalFuns.op30 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_30

theorem retain_31 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op31 (native base) (selected base ops) =
    @ExternalFuns.op31 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_31

theorem retain_32 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op32 (native base) (selected base ops) =
    @ExternalFuns.op32 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_32

theorem retain_33 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op33 (native base) (selected base ops) =
    @ExternalFuns.op33 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_33

theorem retain_34 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op34 (native base) (selected base ops) =
    @ExternalFuns.op34 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_34

theorem retain_35 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op35 (native base) (selected base ops) =
    @ExternalFuns.op35 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_35

theorem retain_36 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op36 (native base) (selected base ops) =
    @ExternalFuns.op36 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_36

theorem retain_38 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op38 (native base) (selected base ops) =
    @ExternalFuns.op38 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_38

theorem retain_39 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op39 (native base) (selected base ops) =
    @ExternalFuns.op39 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_39

theorem retain_42 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op42 (native base) (selected base ops) =
    @ExternalFuns.op42 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_42

theorem retain_45 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op45 (native base) (selected base ops) =
    @ExternalFuns.op45 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_45

theorem retain_46 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op46 (native base) (selected base ops) =
    @ExternalFuns.op46 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_46

theorem retain_47 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op47 (native base) (selected base ops) =
    @ExternalFuns.op47 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_47

theorem retain_48 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op48 (native base) (selected base ops) =
    @ExternalFuns.op48 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_48

theorem retain_51 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op51 (native base) (selected base ops) =
    @ExternalFuns.op51 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_51

theorem retain_52 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op52 (native base) (selected base ops) =
    @ExternalFuns.op52 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_52

theorem retain_53 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op53 (native base) (selected base ops) =
    @ExternalFuns.op53 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_53

theorem retain_54 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op54 (native base) (selected base ops) =
    @ExternalFuns.op54 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_54

theorem retain_55 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op55 (native base) (selected base ops) =
    @ExternalFuns.op55 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_55

theorem retain_56 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op56 (native base) (selected base ops) =
    @ExternalFuns.op56 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_56

theorem retain_57 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op57 (native base) (selected base ops) =
    @ExternalFuns.op57 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_57

theorem retain_58 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op58 (native base) (selected base ops) =
    @ExternalFuns.op58 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_58

theorem retain_59 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op59 (native base) (selected base ops) =
    @ExternalFuns.op59 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_59

theorem retain_61 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op61 (native base) (selected base ops) =
    @ExternalFuns.op61 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_61

theorem retain_62 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op62 (native base) (selected base ops) =
    @ExternalFuns.op62 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_62

theorem retain_63 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op63 (native base) (selected base ops) =
    @ExternalFuns.op63 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_63

theorem retain_64 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op64 (native base) (selected base ops) =
    @ExternalFuns.op64 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_64

theorem retain_65 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op65 (native base) (selected base ops) =
    @ExternalFuns.op65 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_65

theorem retain_66 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op66 (native base) (selected base ops) =
    @ExternalFuns.op66 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_66

theorem retain_67 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op67 (native base) (selected base ops) =
    @ExternalFuns.op67 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_67

theorem retain_68 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op68 (native base) (selected base ops) =
    @ExternalFuns.op68 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_68

theorem retain_69 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op69 (native base) (selected base ops) =
    @ExternalFuns.op69 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_69

theorem retain_70 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op70 (native base) (selected base ops) =
    @ExternalFuns.op70 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_70

theorem retain_71 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op71 (native base) (selected base ops) =
    @ExternalFuns.op71 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_71

theorem retain_72 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op72 (native base) (selected base ops) =
    @ExternalFuns.op72 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_72

theorem retain_73 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op73 (native base) (selected base ops) =
    @ExternalFuns.op73 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_73

theorem retain_74 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op74 (native base) (selected base ops) =
    @ExternalFuns.op74 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_74

theorem retain_75 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op75 (native base) (selected base ops) =
    @ExternalFuns.op75 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_75

theorem retain_76 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op76 (native base) (selected base ops) =
    @ExternalFuns.op76 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_76

theorem retain_77 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op77 (native base) (selected base ops) =
    @ExternalFuns.op77 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_77

theorem retain_78 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op78 (native base) (selected base ops) =
    @ExternalFuns.op78 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_78

theorem retain_79 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op79 (native base) (selected base ops) =
    @ExternalFuns.op79 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_79

theorem retain_80 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op80 (native base) (selected base ops) =
    @ExternalFuns.op80 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_80

theorem retain_81 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op81 (native base) (selected base ops) =
    @ExternalFuns.op81 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_81

theorem retain_82 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op82 (native base) (selected base ops) =
    @ExternalFuns.op82 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_82

theorem retain_83 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op83 (native base) (selected base ops) =
    @ExternalFuns.op83 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_83

theorem retain_84 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op84 (native base) (selected base ops) =
    @ExternalFuns.op84 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_84

theorem retain_85 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op85 (native base) (selected base ops) =
    @ExternalFuns.op85 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_85

theorem retain_86 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op86 (native base) (selected base ops) =
    @ExternalFuns.op86 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_86

theorem retain_87 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op87 (native base) (selected base ops) =
    @ExternalFuns.op87 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_87

theorem retain_88 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op88 (native base) (selected base ops) =
    @ExternalFuns.op88 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_88

theorem retain_89 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op89 (native base) (selected base ops) =
    @ExternalFuns.op89 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_89

theorem retain_90 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op90 (native base) (selected base ops) =
    @ExternalFuns.op90 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_90

theorem retain_91 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op91 (native base) (selected base ops) =
    @ExternalFuns.op91 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_91

theorem retain_92 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op92 (native base) (selected base ops) =
    @ExternalFuns.op92 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_92

theorem retain_93 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op93 (native base) (selected base ops) =
    @ExternalFuns.op93 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_93

theorem retain_94 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op94 (native base) (selected base ops) =
    @ExternalFuns.op94 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_94

theorem retain_95 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op95 (native base) (selected base ops) =
    @ExternalFuns.op95 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_95

theorem retain_96 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op96 (native base) (selected base ops) =
    @ExternalFuns.op96 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_96

theorem retain_97 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op97 (native base) (selected base ops) =
    @ExternalFuns.op97 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_97

theorem retain_98 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op98 (native base) (selected base ops) =
    @ExternalFuns.op98 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_98

theorem retain_99 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op99 (native base) (selected base ops) =
    @ExternalFuns.op99 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_99

theorem retain_100 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op100 (native base) (selected base ops) =
    @ExternalFuns.op100 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_100

theorem retain_101 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op101 (native base) (selected base ops) =
    @ExternalFuns.op101 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_101

theorem retain_102 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op102 (native base) (selected base ops) =
    @ExternalFuns.op102 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_102

theorem retain_103 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op103 (native base) (selected base ops) =
    @ExternalFuns.op103 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_103

theorem retain_104 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op104 (native base) (selected base ops) =
    @ExternalFuns.op104 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_104

theorem retain_105 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op105 (native base) (selected base ops) =
    @ExternalFuns.op105 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_105

theorem retain_106 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op106 (native base) (selected base ops) =
    @ExternalFuns.op106 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_106

theorem retain_107 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op107 (native base) (selected base ops) =
    @ExternalFuns.op107 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_107

theorem retain_108 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op108 (native base) (selected base ops) =
    @ExternalFuns.op108 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_108

theorem retain_109 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op109 (native base) (selected base ops) =
    @ExternalFuns.op109 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_109

theorem retain_110 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op110 (native base) (selected base ops) =
    @ExternalFuns.op110 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_110

theorem retain_111 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op111 (native base) (selected base ops) =
    @ExternalFuns.op111 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_111

theorem retain_112 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op112 (native base) (selected base ops) =
    @ExternalFuns.op112 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_112

theorem retain_113 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op113 (native base) (selected base ops) =
    @ExternalFuns.op113 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_113

theorem retain_114 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op114 (native base) (selected base ops) =
    @ExternalFuns.op114 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_114

theorem retain_115 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op115 (native base) (selected base ops) =
    @ExternalFuns.op115 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_115

theorem retain_116 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op116 (native base) (selected base ops) =
    @ExternalFuns.op116 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_116

theorem retain_117 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op117 (native base) (selected base ops) =
    @ExternalFuns.op117 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_117

theorem retain_118 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op118 (native base) (selected base ops) =
    @ExternalFuns.op118 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_118

theorem retain_119 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op119 (native base) (selected base ops) =
    @ExternalFuns.op119 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_119

theorem retain_120 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op120 (native base) (selected base ops) =
    @ExternalFuns.op120 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_120

theorem retain_121 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op121 (native base) (selected base ops) =
    @ExternalFuns.op121 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_121

theorem retain_122 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op122 (native base) (selected base ops) =
    @ExternalFuns.op122 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_122

theorem retain_123 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op123 (native base) (selected base ops) =
    @ExternalFuns.op123 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_123

theorem retain_124 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op124 (native base) (selected base ops) =
    @ExternalFuns.op124 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_124

theorem retain_125 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op125 (native base) (selected base ops) =
    @ExternalFuns.op125 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_125

theorem retain_126 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op126 (native base) (selected base ops) =
    @ExternalFuns.op126 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_126

theorem retain_127 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op127 (native base) (selected base ops) =
    @ExternalFuns.op127 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_127

theorem retain_128 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op128 (native base) (selected base ops) =
    @ExternalFuns.op128 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_128

theorem retain_129 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op129 (native base) (selected base ops) =
    @ExternalFuns.op129 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_129

theorem retain_130 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op130 (native base) (selected base ops) =
    @ExternalFuns.op130 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_130

theorem retain_131 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op131 (native base) (selected base ops) =
    @ExternalFuns.op131 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_131

theorem retain_132 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op132 (native base) (selected base ops) =
    @ExternalFuns.op132 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_132

theorem retain_133 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op133 (native base) (selected base ops) =
    @ExternalFuns.op133 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_133

theorem retain_134 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op134 (native base) (selected base ops) =
    @ExternalFuns.op134 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_134

theorem retain_135 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op135 (native base) (selected base ops) =
    @ExternalFuns.op135 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_135

theorem retain_136 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op136 (native base) (selected base ops) =
    @ExternalFuns.op136 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_136

theorem retain_137 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op137 (native base) (selected base ops) =
    @ExternalFuns.op137 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_137

theorem retain_138 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op138 (native base) (selected base ops) =
    @ExternalFuns.op138 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_138

theorem retain_139 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op139 (native base) (selected base ops) =
    @ExternalFuns.op139 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_139

theorem retain_140 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op140 (native base) (selected base ops) =
    @ExternalFuns.op140 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_140

theorem retain_141 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op141 (native base) (selected base ops) =
    @ExternalFuns.op141 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_141

theorem retain_142 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op142 (native base) (selected base ops) =
    @ExternalFuns.op142 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_142

theorem retain_143 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op143 (native base) (selected base ops) =
    @ExternalFuns.op143 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_143

theorem retain_144 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op144 (native base) (selected base ops) =
    @ExternalFuns.op144 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_144

theorem retain_145 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op145 (native base) (selected base ops) =
    @ExternalFuns.op145 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_145

theorem retain_146 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op146 (native base) (selected base ops) =
    @ExternalFuns.op146 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_146

theorem retain_147 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op147 (native base) (selected base ops) =
    @ExternalFuns.op147 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_147

theorem retain_148 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op148 (native base) (selected base ops) =
    @ExternalFuns.op148 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_148

theorem retain_149 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op149 (native base) (selected base ops) =
    @ExternalFuns.op149 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_149

theorem retain_150 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op150 (native base) (selected base ops) =
    @ExternalFuns.op150 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_150

theorem retain_151 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op151 (native base) (selected base ops) =
    @ExternalFuns.op151 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_151

theorem retain_152 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op152 (native base) (selected base ops) =
    @ExternalFuns.op152 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_152

theorem retain_153 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op153 (native base) (selected base ops) =
    @ExternalFuns.op153 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_153

theorem retain_154 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op154 (native base) (selected base ops) =
    @ExternalFuns.op154 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_154

theorem retain_155 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op155 (native base) (selected base ops) =
    @ExternalFuns.op155 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_155

theorem retain_156 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op156 (native base) (selected base ops) =
    @ExternalFuns.op156 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_156

theorem retain_157 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op157 (native base) (selected base ops) =
    @ExternalFuns.op157 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_157

theorem retain_158 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op158 (native base) (selected base ops) =
    @ExternalFuns.op158 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_158

theorem retain_159 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op159 (native base) (selected base ops) =
    @ExternalFuns.op159 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_159

theorem retain_160 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op160 (native base) (selected base ops) =
    @ExternalFuns.op160 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_160

theorem retain_161 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op161 (native base) (selected base ops) =
    @ExternalFuns.op161 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_161

theorem retain_162 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op162 (native base) (selected base ops) =
    @ExternalFuns.op162 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_162

theorem retain_163 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op163 (native base) (selected base ops) =
    @ExternalFuns.op163 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_163

theorem retain_164 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op164 (native base) (selected base ops) =
    @ExternalFuns.op164 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_164

theorem retain_165 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op165 (native base) (selected base ops) =
    @ExternalFuns.op165 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_165

theorem retain_166 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op166 (native base) (selected base ops) =
    @ExternalFuns.op166 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_166

theorem retain_167 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op167 (native base) (selected base ops) =
    @ExternalFuns.op167 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_167

theorem retain_168 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op168 (native base) (selected base ops) =
    @ExternalFuns.op168 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_168

theorem retain_169 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op169 (native base) (selected base ops) =
    @ExternalFuns.op169 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_169

theorem retain_170 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op170 (native base) (selected base ops) =
    @ExternalFuns.op170 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_170

theorem retain_171 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op171 (native base) (selected base ops) =
    @ExternalFuns.op171 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_171

theorem retain_172 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op172 (native base) (selected base ops) =
    @ExternalFuns.op172 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_172

theorem retain_173 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op173 (native base) (selected base ops) =
    @ExternalFuns.op173 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_173

theorem retain_174 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op174 (native base) (selected base ops) =
    @ExternalFuns.op174 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_174

theorem retain_175 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op175 (native base) (selected base ops) =
    @ExternalFuns.op175 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_175

theorem retain_176 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op176 (native base) (selected base ops) =
    @ExternalFuns.op176 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_176

theorem retain_177 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op177 (native base) (selected base ops) =
    @ExternalFuns.op177 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_177

theorem retain_178 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op178 (native base) (selected base ops) =
    @ExternalFuns.op178 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_178

theorem retain_179 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op179 (native base) (selected base ops) =
    @ExternalFuns.op179 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_179

theorem retain_180 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op180 (native base) (selected base ops) =
    @ExternalFuns.op180 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_180

theorem retain_181 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op181 (native base) (selected base ops) =
    @ExternalFuns.op181 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_181

theorem retain_182 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op182 (native base) (selected base ops) =
    @ExternalFuns.op182 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_182

theorem retain_183 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op183 (native base) (selected base ops) =
    @ExternalFuns.op183 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_183

theorem retain_184 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op184 (native base) (selected base ops) =
    @ExternalFuns.op184 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_184

theorem retain_185 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op185 (native base) (selected base ops) =
    @ExternalFuns.op185 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_185

theorem retain_186 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op186 (native base) (selected base ops) =
    @ExternalFuns.op186 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_186

theorem retain_187 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op187 (native base) (selected base ops) =
    @ExternalFuns.op187 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_187

theorem retain_188 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op188 (native base) (selected base ops) =
    @ExternalFuns.op188 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_188

theorem retain_189 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op189 (native base) (selected base ops) =
    @ExternalFuns.op189 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_189

theorem retain_190 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op190 (native base) (selected base ops) =
    @ExternalFuns.op190 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_190

theorem retain_191 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op191 (native base) (selected base ops) =
    @ExternalFuns.op191 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_191

theorem retain_192 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op192 (native base) (selected base ops) =
    @ExternalFuns.op192 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_192

theorem retain_193 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op193 (native base) (selected base ops) =
    @ExternalFuns.op193 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_193

theorem retain_194 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op194 (native base) (selected base ops) =
    @ExternalFuns.op194 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_194

theorem retain_195 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op195 (native base) (selected base ops) =
    @ExternalFuns.op195 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_195

theorem retain_196 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op196 (native base) (selected base ops) =
    @ExternalFuns.op196 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_196

theorem retain_197 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op197 (native base) (selected base ops) =
    @ExternalFuns.op197 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_197

theorem retain_198 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op198 (native base) (selected base ops) =
    @ExternalFuns.op198 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_198

theorem retain_199 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op199 (native base) (selected base ops) =
    @ExternalFuns.op199 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_199

theorem retain_200 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op200 (native base) (selected base ops) =
    @ExternalFuns.op200 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_200

theorem retain_201 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op201 (native base) (selected base ops) =
    @ExternalFuns.op201 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_201

theorem retain_202 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op202 (native base) (selected base ops) =
    @ExternalFuns.op202 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_202

theorem retain_203 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op203 (native base) (selected base ops) =
    @ExternalFuns.op203 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_203

theorem retain_204 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op204 (native base) (selected base ops) =
    @ExternalFuns.op204 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_204

theorem retain_205 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op205 (native base) (selected base ops) =
    @ExternalFuns.op205 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_205

theorem retain_206 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op206 (native base) (selected base ops) =
    @ExternalFuns.op206 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_206

theorem retain_207 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op207 (native base) (selected base ops) =
    @ExternalFuns.op207 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_207

theorem retain_208 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op208 (native base) (selected base ops) =
    @ExternalFuns.op208 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_208

theorem retain_209 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op209 (native base) (selected base ops) =
    @ExternalFuns.op209 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_209

theorem retain_210 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op210 (native base) (selected base ops) =
    @ExternalFuns.op210 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_210

theorem retain_211 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op211 (native base) (selected base ops) =
    @ExternalFuns.op211 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_211

theorem retain_212 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op212 (native base) (selected base ops) =
    @ExternalFuns.op212 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_212

theorem retain_213 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op213 (native base) (selected base ops) =
    @ExternalFuns.op213 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_213

theorem retain_214 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op214 (native base) (selected base ops) =
    @ExternalFuns.op214 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_214

theorem retain_215 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op215 (native base) (selected base ops) =
    @ExternalFuns.op215 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_215

theorem retain_216 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op216 (native base) (selected base ops) =
    @ExternalFuns.op216 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_216

theorem retain_217 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op217 (native base) (selected base ops) =
    @ExternalFuns.op217 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_217

theorem retain_218 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op218 (native base) (selected base ops) =
    @ExternalFuns.op218 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_218

theorem retain_219 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op219 (native base) (selected base ops) =
    @ExternalFuns.op219 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_219

theorem retain_220 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op220 (native base) (selected base ops) =
    @ExternalFuns.op220 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_220

theorem retain_221 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op221 (native base) (selected base ops) =
    @ExternalFuns.op221 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_221

theorem retain_222 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op222 (native base) (selected base ops) =
    @ExternalFuns.op222 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_222

theorem retain_223 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op223 (native base) (selected base ops) =
    @ExternalFuns.op223 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_223

theorem retain_224 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op224 (native base) (selected base ops) =
    @ExternalFuns.op224 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_224

theorem retain_225 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op225 (native base) (selected base ops) =
    @ExternalFuns.op225 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_225

theorem retain_226 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op226 (native base) (selected base ops) =
    @ExternalFuns.op226 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_226

theorem retain_227 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op227 (native base) (selected base ops) =
    @ExternalFuns.op227 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_227

theorem retain_228 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op228 (native base) (selected base ops) =
    @ExternalFuns.op228 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_228

theorem retain_229 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op229 (native base) (selected base ops) =
    @ExternalFuns.op229 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_229

theorem retain_230 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op230 (native base) (selected base ops) =
    @ExternalFuns.op230 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_230

theorem retain_231 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op231 (native base) (selected base ops) =
    @ExternalFuns.op231 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_231

theorem retain_232 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op232 (native base) (selected base ops) =
    @ExternalFuns.op232 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_232

theorem retain_233 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op233 (native base) (selected base ops) =
    @ExternalFuns.op233 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_233

theorem retain_234 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op234 (native base) (selected base ops) =
    @ExternalFuns.op234 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_234

theorem retain_237 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op237 (native base) (selected base ops) =
    @ExternalFuns.op237 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_237

theorem retain_238 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op238 (native base) (selected base ops) =
    @ExternalFuns.op238 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_238

theorem retain_241 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op241 (native base) (selected base ops) =
    @ExternalFuns.op241 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_241

theorem retain_242 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op242 (native base) (selected base ops) =
    @ExternalFuns.op242 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_242

theorem retain_243 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op243 (native base) (selected base ops) =
    @ExternalFuns.op243 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_243

theorem retain_244 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op244 (native base) (selected base ops) =
    @ExternalFuns.op244 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_244

theorem retain_245 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op245 (native base) (selected base ops) =
    @ExternalFuns.op245 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_245

theorem retain_246 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op246 (native base) (selected base ops) =
    @ExternalFuns.op246 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_246

theorem retain_247 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op247 (native base) (selected base ops) =
    @ExternalFuns.op247 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_247

theorem retain_248 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op248 (native base) (selected base ops) =
    @ExternalFuns.op248 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_248

theorem retain_249 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op249 (native base) (selected base ops) =
    @ExternalFuns.op249 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_249

theorem retain_250 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op250 (native base) (selected base ops) =
    @ExternalFuns.op250 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_250

theorem retain_251 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op251 (native base) (selected base ops) =
    @ExternalFuns.op251 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_251

theorem retain_252 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op252 (native base) (selected base ops) =
    @ExternalFuns.op252 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_252

theorem retain_253 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op253 (native base) (selected base ops) =
    @ExternalFuns.op253 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_253

theorem retain_254 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op254 (native base) (selected base ops) =
    @ExternalFuns.op254 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_254

theorem retain_255 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op255 (native base) (selected base ops) =
    @ExternalFuns.op255 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_255

theorem retain_256 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op256 (native base) (selected base ops) =
    @ExternalFuns.op256 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_256

theorem retain_257 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op257 (native base) (selected base ops) =
    @ExternalFuns.op257 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_257

theorem retain_258 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op258 (native base) (selected base ops) =
    @ExternalFuns.op258 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_258

theorem retain_259 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op259 (native base) (selected base ops) =
    @ExternalFuns.op259 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_259

theorem retain_261 (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op261 (native base) (selected base ops) =
    @ExternalFuns.op261 (native base) (PDict_RejectionStd.selected base ops) := rfl
#print axioms retain_261
end R1Z.PDict_CurrentRetention
