import R1Z.PDict_RejectValues
import R1Z.PDict_RejectTreeBridge
import R1Z.PDict_ClientFormatterIndependent
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_SelectorCoherence
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PDict_RejectionStd.native
abbrev selected := PDict_RejectionStd.selected

theorem op0_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op0 (native base) (selected base ops) =
      @ExternalFuns.op0 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op1_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op1 (native base) (selected base ops) =
      @ExternalFuns.op1 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op2_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op2 (native base) (selected base ops) =
      @ExternalFuns.op2 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op13_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op13 (native base) (selected base ops) =
      @ExternalFuns.op13 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op14_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op14 (native base) (selected base ops) =
      @ExternalFuns.op14 (native base) (ops) := rfl

theorem op15_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op15 (native base) (selected base ops) =
      @ExternalFuns.op15 (native base) (ops) := rfl

theorem op17_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op17 (native base) (selected base ops) =
      @ExternalFuns.op17 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op19_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op19 (native base) (selected base ops) =
      @ExternalFuns.op19 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op20_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op20 (native base) (selected base ops) =
      @ExternalFuns.op20 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op21_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op21 (native base) (selected base ops) =
      @ExternalFuns.op21 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op22_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op22 (native base) (selected base ops) =
      @ExternalFuns.op22 (native base) (ops) := rfl

theorem op23_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op23 (native base) (selected base ops) =
      @ExternalFuns.op23 (native base) (ops) := rfl

theorem op24_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op24 (native base) (selected base ops) =
      @ExternalFuns.op24 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op25_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op25 (native base) (selected base ops) =
      @ExternalFuns.op25 (native base) (ops) := rfl

theorem op26_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op26 (native base) (selected base ops) =
      @ExternalFuns.op26 (native base) (ops) := rfl

theorem op27_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op27 (native base) (selected base ops) =
      @ExternalFuns.op27 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op28_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op28 (native base) (selected base ops) =
      @ExternalFuns.op28 (native base) (ops) := rfl

theorem op29_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op29 (native base) (selected base ops) =
      @ExternalFuns.op29 (native base) (ops) := rfl

theorem op30_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op30 (native base) (selected base ops) =
      @ExternalFuns.op30 (native base) (ops) := rfl

theorem op31_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op31 (native base) (selected base ops) =
      @ExternalFuns.op31 (native base) (ops) := rfl

theorem op124_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op124 (native base) (selected base ops) =
      @ExternalFuns.op124 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op125_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op125 (native base) (selected base ops) =
      @ExternalFuns.op125 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op126_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op126 (native base) (selected base ops) =
      @ExternalFuns.op126 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op135_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op135 (native base) (selected base ops) =
      @ExternalFuns.op135 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op136_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op136 (native base) (selected base ops) =
      @ExternalFuns.op136 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op137_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op137 (native base) (selected base ops) =
      @ExternalFuns.op137 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op138_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op138 (native base) (selected base ops) =
      @ExternalFuns.op138 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op139_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op139 (native base) (selected base ops) =
      @ExternalFuns.op139 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op140_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op140 (native base) (selected base ops) =
      @ExternalFuns.op140 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op141_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op141 (native base) (selected base ops) =
      @ExternalFuns.op141 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op142_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op142 (native base) (selected base ops) =
      @ExternalFuns.op142 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op143_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op143 (native base) (selected base ops) =
      @ExternalFuns.op143 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op144_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op144 (native base) (selected base ops) =
      @ExternalFuns.op144 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op145_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op145 (native base) (selected base ops) =
      @ExternalFuns.op145 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op146_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op146 (native base) (selected base ops) =
      @ExternalFuns.op146 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op147_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op147 (native base) (selected base ops) =
      @ExternalFuns.op147 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op148_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op148 (native base) (selected base ops) =
      @ExternalFuns.op148 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op149_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op149 (native base) (selected base ops) =
      @ExternalFuns.op149 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op150_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op150 (native base) (selected base ops) =
      @ExternalFuns.op150 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op151_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op151 (native base) (selected base ops) =
      @ExternalFuns.op151 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op152_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op152 (native base) (selected base ops) =
      @ExternalFuns.op152 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op153_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op153 (native base) (selected base ops) =
      @ExternalFuns.op153 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op154_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op154 (native base) (selected base ops) =
      @ExternalFuns.op154 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op155_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op155 (native base) (selected base ops) =
      @ExternalFuns.op155 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op156_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op156 (native base) (selected base ops) =
      @ExternalFuns.op156 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op157_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op157 (native base) (selected base ops) =
      @ExternalFuns.op157 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op158_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op158 (native base) (selected base ops) =
      @ExternalFuns.op158 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op159_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op159 (native base) (selected base ops) =
      @ExternalFuns.op159 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op160_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op160 (native base) (selected base ops) =
      @ExternalFuns.op160 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op161_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op161 (native base) (selected base ops) =
      @ExternalFuns.op161 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op162_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op162 (native base) (selected base ops) =
      @ExternalFuns.op162 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op163_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op163 (native base) (selected base ops) =
      @ExternalFuns.op163 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op164_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op164 (native base) (selected base ops) =
      @ExternalFuns.op164 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op165_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op165 (native base) (selected base ops) =
      @ExternalFuns.op165 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op166_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op166 (native base) (selected base ops) =
      @ExternalFuns.op166 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op167_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op167 (native base) (selected base ops) =
      @ExternalFuns.op167 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op168_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op168 (native base) (selected base ops) =
      @ExternalFuns.op168 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op169_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op169 (native base) (selected base ops) =
      @ExternalFuns.op169 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op170_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op170 (native base) (selected base ops) =
      @ExternalFuns.op170 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op171_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op171 (native base) (selected base ops) =
      @ExternalFuns.op171 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op172_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op172 (native base) (selected base ops) =
      @ExternalFuns.op172 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op173_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op173 (native base) (selected base ops) =
      @ExternalFuns.op173 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op174_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op174 (native base) (selected base ops) =
      @ExternalFuns.op174 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op175_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op175 (native base) (selected base ops) =
      @ExternalFuns.op175 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op176_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op176 (native base) (selected base ops) =
      @ExternalFuns.op176 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op177_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op177 (native base) (selected base ops) =
      @ExternalFuns.op177 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op178_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op178 (native base) (selected base ops) =
      @ExternalFuns.op178 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op179_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op179 (native base) (selected base ops) =
      @ExternalFuns.op179 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op180_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op180 (native base) (selected base ops) =
      @ExternalFuns.op180 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op181_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op181 (native base) (selected base ops) =
      @ExternalFuns.op181 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op182_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op182 (native base) (selected base ops) =
      @ExternalFuns.op182 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op183_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op183 (native base) (selected base ops) =
      @ExternalFuns.op183 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op184_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op184 (native base) (selected base ops) =
      @ExternalFuns.op184 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op185_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op185 (native base) (selected base ops) =
      @ExternalFuns.op185 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op186_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op186 (native base) (selected base ops) =
      @ExternalFuns.op186 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op187_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op187 (native base) (selected base ops) =
      @ExternalFuns.op187 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op188_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op188 (native base) (selected base ops) =
      @ExternalFuns.op188 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op189_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op189 (native base) (selected base ops) =
      @ExternalFuns.op189 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op190_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op190 (native base) (selected base ops) =
      @ExternalFuns.op190 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op191_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op191 (native base) (selected base ops) =
      @ExternalFuns.op191 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op192_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op192 (native base) (selected base ops) =
      @ExternalFuns.op192 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op193_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op193 (native base) (selected base ops) =
      @ExternalFuns.op193 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op194_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op194 (native base) (selected base ops) =
      @ExternalFuns.op194 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op195_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op195 (native base) (selected base ops) =
      @ExternalFuns.op195 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op196_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op196 (native base) (selected base ops) =
      @ExternalFuns.op196 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op197_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op197 (native base) (selected base ops) =
      @ExternalFuns.op197 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op198_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op198 (native base) (selected base ops) =
      @ExternalFuns.op198 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op199_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op199 (native base) (selected base ops) =
      @ExternalFuns.op199 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op200_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op200 (native base) (selected base ops) =
      @ExternalFuns.op200 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op201_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op201 (native base) (selected base ops) =
      @ExternalFuns.op201 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op202_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op202 (native base) (selected base ops) =
      @ExternalFuns.op202 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op203_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op203 (native base) (selected base ops) =
      @ExternalFuns.op203 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op204_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op204 (native base) (selected base ops) =
      @ExternalFuns.op204 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op205_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op205 (native base) (selected base ops) =
      @ExternalFuns.op205 (native base) (ops) := rfl

theorem op206_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op206 (native base) (selected base ops) =
      @ExternalFuns.op206 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op207_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op207 (native base) (selected base ops) =
      @ExternalFuns.op207 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op208_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op208 (native base) (selected base ops) =
      @ExternalFuns.op208 (native base) (ops) := rfl

theorem op209_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op209 (native base) (selected base ops) =
      @ExternalFuns.op209 (native base) (ops) := rfl

theorem op210_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op210 (native base) (selected base ops) =
      @ExternalFuns.op210 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op211_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op211 (native base) (selected base ops) =
      @ExternalFuns.op211 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op212_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op212 (native base) (selected base ops) =
      @ExternalFuns.op212 (native base) (ops) := rfl

theorem op213_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op213 (native base) (selected base ops) =
      @ExternalFuns.op213 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op214_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op214 (native base) (selected base ops) =
      @ExternalFuns.op214 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op215_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op215 (native base) (selected base ops) =
      @ExternalFuns.op215 (native base) (ops) := rfl

theorem op216_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op216 (native base) (selected base ops) =
      @ExternalFuns.op216 (native base) (ops) := rfl

theorem op217_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op217 (native base) (selected base ops) =
      @ExternalFuns.op217 (native base) (ops) := rfl

theorem op218_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op218 (native base) (selected base ops) =
      @ExternalFuns.op218 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op219_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op219 (native base) (selected base ops) =
      @ExternalFuns.op219 (native base) (ops) := rfl

theorem op220_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op220 (native base) (selected base ops) =
      @ExternalFuns.op220 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op221_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op221 (native base) (selected base ops) =
      @ExternalFuns.op221 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op238_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op238 (native base) (selected base ops) =
      @ExternalFuns.op238 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op256_retained (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op256 (native base) (selected base ops) =
      @ExternalFuns.op256 (native base) (PDict_FileCarrier.selected base ops) := rfl

theorem op261_still_open (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @ExternalFuns.op261 (native base) (selected base ops) =
      @ExternalFuns.op261 (native base) (ops) := rfl

/-- Debug independence applies to the complete final selected caller. Native
IO/world and the global real RunJoin are deliberately not inferred here. -/
theorem client_without_debug (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) :
    @RealR1_client.prove_for_proof_accounts (native base)
      (@PDict_FormatterIndependent.erased (native base) (selected base ops)) =
    @RealR1_client.prove_for_proof_accounts (native base) (selected base ops) :=
  @PDict_ClientFormatterIndependent.client_erased (native base) (selected base ops)

#print axioms op0_retained
#print axioms op1_retained
#print axioms op2_retained
#print axioms op13_retained
#print axioms op14_still_open
#print axioms op15_still_open
#print axioms op17_retained
#print axioms op19_retained
#print axioms op20_retained
#print axioms op21_retained
#print axioms op22_still_open
#print axioms op23_still_open
#print axioms op24_retained
#print axioms op25_still_open
#print axioms op26_still_open
#print axioms op27_retained
#print axioms op28_still_open
#print axioms op29_still_open
#print axioms op30_still_open
#print axioms op31_still_open
#print axioms op124_retained
#print axioms op125_retained
#print axioms op126_retained
#print axioms op135_retained
#print axioms op136_retained
#print axioms op137_retained
#print axioms op138_retained
#print axioms op139_retained
#print axioms op140_retained
#print axioms op141_retained
#print axioms op142_retained
#print axioms op143_retained
#print axioms op144_retained
#print axioms op145_retained
#print axioms op146_retained
#print axioms op147_retained
#print axioms op148_retained
#print axioms op149_retained
#print axioms op150_retained
#print axioms op151_retained
#print axioms op152_retained
#print axioms op153_retained
#print axioms op154_retained
#print axioms op155_retained
#print axioms op156_retained
#print axioms op157_retained
#print axioms op158_retained
#print axioms op159_retained
#print axioms op160_retained
#print axioms op161_retained
#print axioms op162_retained
#print axioms op163_retained
#print axioms op164_retained
#print axioms op165_retained
#print axioms op166_retained
#print axioms op167_retained
#print axioms op168_retained
#print axioms op169_retained
#print axioms op170_retained
#print axioms op171_retained
#print axioms op172_retained
#print axioms op173_retained
#print axioms op174_retained
#print axioms op175_retained
#print axioms op176_retained
#print axioms op177_retained
#print axioms op178_retained
#print axioms op179_retained
#print axioms op180_retained
#print axioms op181_retained
#print axioms op182_retained
#print axioms op183_retained
#print axioms op184_retained
#print axioms op185_retained
#print axioms op186_retained
#print axioms op187_retained
#print axioms op188_retained
#print axioms op189_retained
#print axioms op190_retained
#print axioms op191_retained
#print axioms op192_retained
#print axioms op193_retained
#print axioms op194_retained
#print axioms op195_retained
#print axioms op196_retained
#print axioms op197_retained
#print axioms op198_retained
#print axioms op199_retained
#print axioms op200_retained
#print axioms op201_retained
#print axioms op202_retained
#print axioms op203_retained
#print axioms op204_retained
#print axioms op205_still_open
#print axioms op206_retained
#print axioms op207_retained
#print axioms op208_still_open
#print axioms op209_still_open
#print axioms op210_retained
#print axioms op211_retained
#print axioms op212_still_open
#print axioms op213_retained
#print axioms op214_retained
#print axioms op215_still_open
#print axioms op216_still_open
#print axioms op217_still_open
#print axioms op218_retained
#print axioms op219_still_open
#print axioms op220_retained
#print axioms op221_retained
#print axioms op238_retained
#print axioms op256_retained
#print axioms op261_still_open
#print axioms client_without_debug
end R1Z.PDict_SelectorCoherence
