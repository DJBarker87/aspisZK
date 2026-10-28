import R1Z.PV_B2_E_OrdinaryOriginal
import R1Z.ProverRwFullExternalFuns
set_option autoImplicit false
namespace PV_B2_E_Install250
open Aeneas Aeneas.Std Result ProverRwFull PV_B2_E_OrdinaryOriginal
variable [ExternalTypes]
def callback (b : Bytes) : Result Native :=
  mapResult toNative (PV_B2_C_Sampler.host_sampler.ordinary_sample b)
def selected (ops : ExternalFuns) : ExternalFuns := {ops with op250 := callback}
def originalDictionary (ops : ExternalFuns) : ExternalFuns :=
  {ops with op250 := fun b => mapResult toNative (original b)}

theorem selected_callback (ops : ExternalFuns) (b : Bytes) :
    (selected ops).op250 b = mapResult toNative (original b) := by
  change mapResult toNative _ = _
  rw [copy_equal_original]

theorem nonfailure (ops : ExternalFuns) (b : Bytes) :
    ∃ out, (selected ops).op250 b = ok out := by
  obtain ⟨a,he,_⟩ := native_result b
  exact ⟨toNative (PV_B2_C_ArrayDigits.raw a),he⟩

theorem value_law (ops : ExternalFuns) (b : Bytes) :
    ∃ a : Digits, (selected ops).op250 b = ok (toNative (PV_B2_C_ArrayDigits.raw a)) ∧
      AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge.values a =
        AspisR1.SamplerNatModel.ordinaryDigits (AspisR1.SourceSamplerByteRank.rank b) :=
  native_result b

theorem nonvacuity (ops : ExternalFuns) :
    ∃ out, (selected ops).op250 (Array.repeat 32#usize 0#u8) = ok out :=
  nonfailure ops _

theorem dictionaries (ops : ExternalFuns) : selected ops = originalDictionary ops := by
  have he : callback = (fun b => mapResult toNative (original b)) := by
    funext b
    exact selected_callback ops b
  unfold selected originalDictionary
  rw [he]

theorem observations {O : Sort _} (observe : ExternalFuns → O) (ops : ExternalFuns) :
    observe (selected ops) = observe (originalDictionary ops) :=
  congrArg observe (dictionaries ops)

theorem result_observations {O : Sort _} (observe : Result Native → O)
    (ops : ExternalFuns) (b : Bytes) :
    observe ((selected ops).op250 b) = observe (mapResult toNative (original b)) :=
  congrArg observe (selected_callback ops b)
theorem preserved_0 (ops : ExternalFuns) : (selected ops).op0 = ops.op0 := rfl
theorem preserved_1 (ops : ExternalFuns) : (selected ops).op1 = ops.op1 := rfl
theorem preserved_2 (ops : ExternalFuns) : (selected ops).op2 = ops.op2 := rfl
theorem preserved_3 (ops : ExternalFuns) : (selected ops).op3 = ops.op3 := rfl
theorem preserved_4 (ops : ExternalFuns) : (selected ops).op4 = ops.op4 := rfl
theorem preserved_5 (ops : ExternalFuns) : (selected ops).op5 = ops.op5 := rfl
theorem preserved_6 (ops : ExternalFuns) : (selected ops).op6 = ops.op6 := rfl
theorem preserved_7 (ops : ExternalFuns) : (selected ops).op7 = ops.op7 := rfl
theorem preserved_8 (ops : ExternalFuns) : (selected ops).op8 = ops.op8 := rfl
theorem preserved_9 (ops : ExternalFuns) : (selected ops).op9 = ops.op9 := rfl
theorem preserved_10 (ops : ExternalFuns) : (selected ops).op10 = ops.op10 := rfl
theorem preserved_11 (ops : ExternalFuns) : (selected ops).op11 = ops.op11 := rfl
theorem preserved_12 (ops : ExternalFuns) : (selected ops).op12 = ops.op12 := rfl
theorem preserved_13 (ops : ExternalFuns) : (selected ops).op13 = ops.op13 := rfl
theorem preserved_14 (ops : ExternalFuns) : (selected ops).op14 = ops.op14 := rfl
theorem preserved_15 (ops : ExternalFuns) : (selected ops).op15 = ops.op15 := rfl
theorem preserved_16 (ops : ExternalFuns) : (selected ops).op16 = ops.op16 := rfl
theorem preserved_17 (ops : ExternalFuns) : (selected ops).op17 = ops.op17 := rfl
theorem preserved_18 (ops : ExternalFuns) : (selected ops).op18 = ops.op18 := rfl
theorem preserved_19 (ops : ExternalFuns) : (selected ops).op19 = ops.op19 := rfl
theorem preserved_20 (ops : ExternalFuns) : (selected ops).op20 = ops.op20 := rfl
theorem preserved_21 (ops : ExternalFuns) : (selected ops).op21 = ops.op21 := rfl
theorem preserved_22 (ops : ExternalFuns) : (selected ops).op22 = ops.op22 := rfl
theorem preserved_23 (ops : ExternalFuns) : (selected ops).op23 = ops.op23 := rfl
theorem preserved_24 (ops : ExternalFuns) : (selected ops).op24 = ops.op24 := rfl
theorem preserved_25 (ops : ExternalFuns) : (selected ops).op25 = ops.op25 := rfl
theorem preserved_26 (ops : ExternalFuns) : (selected ops).op26 = ops.op26 := rfl
theorem preserved_27 (ops : ExternalFuns) : (selected ops).op27 = ops.op27 := rfl
theorem preserved_28 (ops : ExternalFuns) : (selected ops).op28 = ops.op28 := rfl
theorem preserved_29 (ops : ExternalFuns) : (selected ops).op29 = ops.op29 := rfl
theorem preserved_30 (ops : ExternalFuns) : (selected ops).op30 = ops.op30 := rfl
theorem preserved_31 (ops : ExternalFuns) : (selected ops).op31 = ops.op31 := rfl
theorem preserved_32 (ops : ExternalFuns) : (selected ops).op32 = ops.op32 := rfl
theorem preserved_33 (ops : ExternalFuns) : (selected ops).op33 = ops.op33 := rfl
theorem preserved_34 (ops : ExternalFuns) : (selected ops).op34 = ops.op34 := rfl
theorem preserved_35 (ops : ExternalFuns) : (selected ops).op35 = ops.op35 := rfl
theorem preserved_36 (ops : ExternalFuns) : (selected ops).op36 = ops.op36 := rfl
theorem preserved_37 (ops : ExternalFuns) : (selected ops).op37 = ops.op37 := rfl
theorem preserved_38 (ops : ExternalFuns) : (selected ops).op38 = ops.op38 := rfl
theorem preserved_39 (ops : ExternalFuns) : (selected ops).op39 = ops.op39 := rfl
theorem preserved_40 (ops : ExternalFuns) : (selected ops).op40 = ops.op40 := rfl
theorem preserved_41 (ops : ExternalFuns) : (selected ops).op41 = ops.op41 := rfl
theorem preserved_42 (ops : ExternalFuns) : (selected ops).op42 = ops.op42 := rfl
theorem preserved_43 (ops : ExternalFuns) : (selected ops).op43 = ops.op43 := rfl
theorem preserved_44 (ops : ExternalFuns) : (selected ops).op44 = ops.op44 := rfl
theorem preserved_45 (ops : ExternalFuns) : (selected ops).op45 = ops.op45 := rfl
theorem preserved_46 (ops : ExternalFuns) : (selected ops).op46 = ops.op46 := rfl
theorem preserved_47 (ops : ExternalFuns) : (selected ops).op47 = ops.op47 := rfl
theorem preserved_48 (ops : ExternalFuns) : (selected ops).op48 = ops.op48 := rfl
theorem preserved_49 (ops : ExternalFuns) : (selected ops).op49 = ops.op49 := rfl
theorem preserved_50 (ops : ExternalFuns) : (selected ops).op50 = ops.op50 := rfl
theorem preserved_51 (ops : ExternalFuns) : (selected ops).op51 = ops.op51 := rfl
theorem preserved_52 (ops : ExternalFuns) : (selected ops).op52 = ops.op52 := rfl
theorem preserved_53 (ops : ExternalFuns) : (selected ops).op53 = ops.op53 := rfl
theorem preserved_54 (ops : ExternalFuns) : (selected ops).op54 = ops.op54 := rfl
theorem preserved_55 (ops : ExternalFuns) : (selected ops).op55 = ops.op55 := rfl
theorem preserved_56 (ops : ExternalFuns) : (selected ops).op56 = ops.op56 := rfl
theorem preserved_57 (ops : ExternalFuns) : (selected ops).op57 = ops.op57 := rfl
theorem preserved_58 (ops : ExternalFuns) : (selected ops).op58 = ops.op58 := rfl
theorem preserved_59 (ops : ExternalFuns) : (selected ops).op59 = ops.op59 := rfl
theorem preserved_60 (ops : ExternalFuns) : (selected ops).op60 = ops.op60 := rfl
theorem preserved_61 (ops : ExternalFuns) : (selected ops).op61 = ops.op61 := rfl
theorem preserved_62 (ops : ExternalFuns) : (selected ops).op62 = ops.op62 := rfl
theorem preserved_63 (ops : ExternalFuns) : (selected ops).op63 = ops.op63 := rfl
theorem preserved_64 (ops : ExternalFuns) : (selected ops).op64 = ops.op64 := rfl
theorem preserved_65 (ops : ExternalFuns) : (selected ops).op65 = ops.op65 := rfl
theorem preserved_66 (ops : ExternalFuns) : (selected ops).op66 = ops.op66 := rfl
theorem preserved_67 (ops : ExternalFuns) : (selected ops).op67 = ops.op67 := rfl
theorem preserved_68 (ops : ExternalFuns) : (selected ops).op68 = ops.op68 := rfl
theorem preserved_69 (ops : ExternalFuns) : (selected ops).op69 = ops.op69 := rfl
theorem preserved_70 (ops : ExternalFuns) : (selected ops).op70 = ops.op70 := rfl
theorem preserved_71 (ops : ExternalFuns) : (selected ops).op71 = ops.op71 := rfl
theorem preserved_72 (ops : ExternalFuns) : (selected ops).op72 = ops.op72 := rfl
theorem preserved_73 (ops : ExternalFuns) : (selected ops).op73 = ops.op73 := rfl
theorem preserved_74 (ops : ExternalFuns) : (selected ops).op74 = ops.op74 := rfl
theorem preserved_75 (ops : ExternalFuns) : (selected ops).op75 = ops.op75 := rfl
theorem preserved_76 (ops : ExternalFuns) : (selected ops).op76 = ops.op76 := rfl
theorem preserved_77 (ops : ExternalFuns) : (selected ops).op77 = ops.op77 := rfl
theorem preserved_78 (ops : ExternalFuns) : (selected ops).op78 = ops.op78 := rfl
theorem preserved_79 (ops : ExternalFuns) : (selected ops).op79 = ops.op79 := rfl
theorem preserved_80 (ops : ExternalFuns) : (selected ops).op80 = ops.op80 := rfl
theorem preserved_81 (ops : ExternalFuns) : (selected ops).op81 = ops.op81 := rfl
theorem preserved_82 (ops : ExternalFuns) : (selected ops).op82 = ops.op82 := rfl
theorem preserved_83 (ops : ExternalFuns) : (selected ops).op83 = ops.op83 := rfl
theorem preserved_84 (ops : ExternalFuns) : (selected ops).op84 = ops.op84 := rfl
theorem preserved_85 (ops : ExternalFuns) : (selected ops).op85 = ops.op85 := rfl
theorem preserved_86 (ops : ExternalFuns) : (selected ops).op86 = ops.op86 := rfl
theorem preserved_87 (ops : ExternalFuns) : (selected ops).op87 = ops.op87 := rfl
theorem preserved_88 (ops : ExternalFuns) : (selected ops).op88 = ops.op88 := rfl
theorem preserved_89 (ops : ExternalFuns) : (selected ops).op89 = ops.op89 := rfl
theorem preserved_90 (ops : ExternalFuns) : (selected ops).op90 = ops.op90 := rfl
theorem preserved_91 (ops : ExternalFuns) : (selected ops).op91 = ops.op91 := rfl
theorem preserved_92 (ops : ExternalFuns) : (selected ops).op92 = ops.op92 := rfl
theorem preserved_93 (ops : ExternalFuns) : (selected ops).op93 = ops.op93 := rfl
theorem preserved_94 (ops : ExternalFuns) : (selected ops).op94 = ops.op94 := rfl
theorem preserved_95 (ops : ExternalFuns) : (selected ops).op95 = ops.op95 := rfl
theorem preserved_96 (ops : ExternalFuns) : (selected ops).op96 = ops.op96 := rfl
theorem preserved_97 (ops : ExternalFuns) : (selected ops).op97 = ops.op97 := rfl
theorem preserved_98 (ops : ExternalFuns) : (selected ops).op98 = ops.op98 := rfl
theorem preserved_99 (ops : ExternalFuns) : (selected ops).op99 = ops.op99 := rfl
theorem preserved_100 (ops : ExternalFuns) : (selected ops).op100 = ops.op100 := rfl
theorem preserved_101 (ops : ExternalFuns) : (selected ops).op101 = ops.op101 := rfl
theorem preserved_102 (ops : ExternalFuns) : (selected ops).op102 = ops.op102 := rfl
theorem preserved_103 (ops : ExternalFuns) : (selected ops).op103 = ops.op103 := rfl
theorem preserved_104 (ops : ExternalFuns) : (selected ops).op104 = ops.op104 := rfl
theorem preserved_105 (ops : ExternalFuns) : (selected ops).op105 = ops.op105 := rfl
theorem preserved_106 (ops : ExternalFuns) : (selected ops).op106 = ops.op106 := rfl
theorem preserved_107 (ops : ExternalFuns) : (selected ops).op107 = ops.op107 := rfl
theorem preserved_108 (ops : ExternalFuns) : (selected ops).op108 = ops.op108 := rfl
theorem preserved_109 (ops : ExternalFuns) : (selected ops).op109 = ops.op109 := rfl
theorem preserved_110 (ops : ExternalFuns) : (selected ops).op110 = ops.op110 := rfl
theorem preserved_111 (ops : ExternalFuns) : (selected ops).op111 = ops.op111 := rfl
theorem preserved_112 (ops : ExternalFuns) : (selected ops).op112 = ops.op112 := rfl
theorem preserved_113 (ops : ExternalFuns) : (selected ops).op113 = ops.op113 := rfl
theorem preserved_114 (ops : ExternalFuns) : (selected ops).op114 = ops.op114 := rfl
theorem preserved_115 (ops : ExternalFuns) : (selected ops).op115 = ops.op115 := rfl
theorem preserved_116 (ops : ExternalFuns) : (selected ops).op116 = ops.op116 := rfl
theorem preserved_117 (ops : ExternalFuns) : (selected ops).op117 = ops.op117 := rfl
theorem preserved_118 (ops : ExternalFuns) : (selected ops).op118 = ops.op118 := rfl
theorem preserved_119 (ops : ExternalFuns) : (selected ops).op119 = ops.op119 := rfl
theorem preserved_120 (ops : ExternalFuns) : (selected ops).op120 = ops.op120 := rfl
theorem preserved_121 (ops : ExternalFuns) : (selected ops).op121 = ops.op121 := rfl
theorem preserved_122 (ops : ExternalFuns) : (selected ops).op122 = ops.op122 := rfl
theorem preserved_123 (ops : ExternalFuns) : (selected ops).op123 = ops.op123 := rfl
theorem preserved_124 (ops : ExternalFuns) : (selected ops).op124 = ops.op124 := rfl
theorem preserved_125 (ops : ExternalFuns) : (selected ops).op125 = ops.op125 := rfl
theorem preserved_126 (ops : ExternalFuns) : (selected ops).op126 = ops.op126 := rfl
theorem preserved_127 (ops : ExternalFuns) : (selected ops).op127 = ops.op127 := rfl
theorem preserved_128 (ops : ExternalFuns) : (selected ops).op128 = ops.op128 := rfl
theorem preserved_129 (ops : ExternalFuns) : (selected ops).op129 = ops.op129 := rfl
theorem preserved_130 (ops : ExternalFuns) : (selected ops).op130 = ops.op130 := rfl
theorem preserved_131 (ops : ExternalFuns) : (selected ops).op131 = ops.op131 := rfl
theorem preserved_132 (ops : ExternalFuns) : (selected ops).op132 = ops.op132 := rfl
theorem preserved_133 (ops : ExternalFuns) : (selected ops).op133 = ops.op133 := rfl
theorem preserved_134 (ops : ExternalFuns) : (selected ops).op134 = ops.op134 := rfl
theorem preserved_135 (ops : ExternalFuns) : (selected ops).op135 = ops.op135 := rfl
theorem preserved_136 (ops : ExternalFuns) : (selected ops).op136 = ops.op136 := rfl
theorem preserved_137 (ops : ExternalFuns) : (selected ops).op137 = ops.op137 := rfl
theorem preserved_138 (ops : ExternalFuns) : (selected ops).op138 = ops.op138 := rfl
theorem preserved_139 (ops : ExternalFuns) : (selected ops).op139 = ops.op139 := rfl
theorem preserved_140 (ops : ExternalFuns) : (selected ops).op140 = ops.op140 := rfl
theorem preserved_141 (ops : ExternalFuns) : (selected ops).op141 = ops.op141 := rfl
theorem preserved_142 (ops : ExternalFuns) : (selected ops).op142 = ops.op142 := rfl
theorem preserved_143 (ops : ExternalFuns) : (selected ops).op143 = ops.op143 := rfl
theorem preserved_144 (ops : ExternalFuns) : (selected ops).op144 = ops.op144 := rfl
theorem preserved_145 (ops : ExternalFuns) : (selected ops).op145 = ops.op145 := rfl
theorem preserved_146 (ops : ExternalFuns) : (selected ops).op146 = ops.op146 := rfl
theorem preserved_147 (ops : ExternalFuns) : (selected ops).op147 = ops.op147 := rfl
theorem preserved_148 (ops : ExternalFuns) : (selected ops).op148 = ops.op148 := rfl
theorem preserved_149 (ops : ExternalFuns) : (selected ops).op149 = ops.op149 := rfl
theorem preserved_150 (ops : ExternalFuns) : (selected ops).op150 = ops.op150 := rfl
theorem preserved_151 (ops : ExternalFuns) : (selected ops).op151 = ops.op151 := rfl
theorem preserved_152 (ops : ExternalFuns) : (selected ops).op152 = ops.op152 := rfl
theorem preserved_153 (ops : ExternalFuns) : (selected ops).op153 = ops.op153 := rfl
theorem preserved_154 (ops : ExternalFuns) : (selected ops).op154 = ops.op154 := rfl
theorem preserved_155 (ops : ExternalFuns) : (selected ops).op155 = ops.op155 := rfl
theorem preserved_156 (ops : ExternalFuns) : (selected ops).op156 = ops.op156 := rfl
theorem preserved_157 (ops : ExternalFuns) : (selected ops).op157 = ops.op157 := rfl
theorem preserved_158 (ops : ExternalFuns) : (selected ops).op158 = ops.op158 := rfl
theorem preserved_159 (ops : ExternalFuns) : (selected ops).op159 = ops.op159 := rfl
theorem preserved_160 (ops : ExternalFuns) : (selected ops).op160 = ops.op160 := rfl
theorem preserved_161 (ops : ExternalFuns) : (selected ops).op161 = ops.op161 := rfl
theorem preserved_162 (ops : ExternalFuns) : (selected ops).op162 = ops.op162 := rfl
theorem preserved_163 (ops : ExternalFuns) : (selected ops).op163 = ops.op163 := rfl
theorem preserved_164 (ops : ExternalFuns) : (selected ops).op164 = ops.op164 := rfl
theorem preserved_165 (ops : ExternalFuns) : (selected ops).op165 = ops.op165 := rfl
theorem preserved_166 (ops : ExternalFuns) : (selected ops).op166 = ops.op166 := rfl
theorem preserved_167 (ops : ExternalFuns) : (selected ops).op167 = ops.op167 := rfl
theorem preserved_168 (ops : ExternalFuns) : (selected ops).op168 = ops.op168 := rfl
theorem preserved_169 (ops : ExternalFuns) : (selected ops).op169 = ops.op169 := rfl
theorem preserved_170 (ops : ExternalFuns) : (selected ops).op170 = ops.op170 := rfl
theorem preserved_171 (ops : ExternalFuns) : (selected ops).op171 = ops.op171 := rfl
theorem preserved_172 (ops : ExternalFuns) : (selected ops).op172 = ops.op172 := rfl
theorem preserved_173 (ops : ExternalFuns) : (selected ops).op173 = ops.op173 := rfl
theorem preserved_174 (ops : ExternalFuns) : (selected ops).op174 = ops.op174 := rfl
theorem preserved_175 (ops : ExternalFuns) : (selected ops).op175 = ops.op175 := rfl
theorem preserved_176 (ops : ExternalFuns) : (selected ops).op176 = ops.op176 := rfl
theorem preserved_177 (ops : ExternalFuns) : (selected ops).op177 = ops.op177 := rfl
theorem preserved_178 (ops : ExternalFuns) : (selected ops).op178 = ops.op178 := rfl
theorem preserved_179 (ops : ExternalFuns) : (selected ops).op179 = ops.op179 := rfl
theorem preserved_180 (ops : ExternalFuns) : (selected ops).op180 = ops.op180 := rfl
theorem preserved_181 (ops : ExternalFuns) : (selected ops).op181 = ops.op181 := rfl
theorem preserved_182 (ops : ExternalFuns) : (selected ops).op182 = ops.op182 := rfl
theorem preserved_183 (ops : ExternalFuns) : (selected ops).op183 = ops.op183 := rfl
theorem preserved_184 (ops : ExternalFuns) : (selected ops).op184 = ops.op184 := rfl
theorem preserved_185 (ops : ExternalFuns) : (selected ops).op185 = ops.op185 := rfl
theorem preserved_186 (ops : ExternalFuns) : (selected ops).op186 = ops.op186 := rfl
theorem preserved_187 (ops : ExternalFuns) : (selected ops).op187 = ops.op187 := rfl
theorem preserved_188 (ops : ExternalFuns) : (selected ops).op188 = ops.op188 := rfl
theorem preserved_189 (ops : ExternalFuns) : (selected ops).op189 = ops.op189 := rfl
theorem preserved_190 (ops : ExternalFuns) : (selected ops).op190 = ops.op190 := rfl
theorem preserved_191 (ops : ExternalFuns) : (selected ops).op191 = ops.op191 := rfl
theorem preserved_192 (ops : ExternalFuns) : (selected ops).op192 = ops.op192 := rfl
theorem preserved_193 (ops : ExternalFuns) : (selected ops).op193 = ops.op193 := rfl
theorem preserved_194 (ops : ExternalFuns) : (selected ops).op194 = ops.op194 := rfl
theorem preserved_195 (ops : ExternalFuns) : (selected ops).op195 = ops.op195 := rfl
theorem preserved_196 (ops : ExternalFuns) : (selected ops).op196 = ops.op196 := rfl
theorem preserved_197 (ops : ExternalFuns) : (selected ops).op197 = ops.op197 := rfl
theorem preserved_198 (ops : ExternalFuns) : (selected ops).op198 = ops.op198 := rfl
theorem preserved_199 (ops : ExternalFuns) : (selected ops).op199 = ops.op199 := rfl
theorem preserved_200 (ops : ExternalFuns) : (selected ops).op200 = ops.op200 := rfl
theorem preserved_201 (ops : ExternalFuns) : (selected ops).op201 = ops.op201 := rfl
theorem preserved_202 (ops : ExternalFuns) : (selected ops).op202 = ops.op202 := rfl
theorem preserved_203 (ops : ExternalFuns) : (selected ops).op203 = ops.op203 := rfl
theorem preserved_204 (ops : ExternalFuns) : (selected ops).op204 = ops.op204 := rfl
theorem preserved_205 (ops : ExternalFuns) : (selected ops).op205 = ops.op205 := rfl
theorem preserved_206 (ops : ExternalFuns) : (selected ops).op206 = ops.op206 := rfl
theorem preserved_207 (ops : ExternalFuns) : (selected ops).op207 = ops.op207 := rfl
theorem preserved_208 (ops : ExternalFuns) : (selected ops).op208 = ops.op208 := rfl
theorem preserved_209 (ops : ExternalFuns) : (selected ops).op209 = ops.op209 := rfl
theorem preserved_210 (ops : ExternalFuns) : (selected ops).op210 = ops.op210 := rfl
theorem preserved_211 (ops : ExternalFuns) : (selected ops).op211 = ops.op211 := rfl
theorem preserved_212 (ops : ExternalFuns) : (selected ops).op212 = ops.op212 := rfl
theorem preserved_213 (ops : ExternalFuns) : (selected ops).op213 = ops.op213 := rfl
theorem preserved_214 (ops : ExternalFuns) : (selected ops).op214 = ops.op214 := rfl
theorem preserved_215 (ops : ExternalFuns) : (selected ops).op215 = ops.op215 := rfl
theorem preserved_216 (ops : ExternalFuns) : (selected ops).op216 = ops.op216 := rfl
theorem preserved_217 (ops : ExternalFuns) : (selected ops).op217 = ops.op217 := rfl
theorem preserved_218 (ops : ExternalFuns) : (selected ops).op218 = ops.op218 := rfl
theorem preserved_219 (ops : ExternalFuns) : (selected ops).op219 = ops.op219 := rfl
theorem preserved_220 (ops : ExternalFuns) : (selected ops).op220 = ops.op220 := rfl
theorem preserved_221 (ops : ExternalFuns) : (selected ops).op221 = ops.op221 := rfl
theorem preserved_222 (ops : ExternalFuns) : (selected ops).op222 = ops.op222 := rfl
theorem preserved_223 (ops : ExternalFuns) : (selected ops).op223 = ops.op223 := rfl
theorem preserved_224 (ops : ExternalFuns) : (selected ops).op224 = ops.op224 := rfl
theorem preserved_225 (ops : ExternalFuns) : (selected ops).op225 = ops.op225 := rfl
theorem preserved_226 (ops : ExternalFuns) : (selected ops).op226 = ops.op226 := rfl
theorem preserved_227 (ops : ExternalFuns) : (selected ops).op227 = ops.op227 := rfl
theorem preserved_228 (ops : ExternalFuns) : (selected ops).op228 = ops.op228 := rfl
theorem preserved_229 (ops : ExternalFuns) : (selected ops).op229 = ops.op229 := rfl
theorem preserved_230 (ops : ExternalFuns) : (selected ops).op230 = ops.op230 := rfl
theorem preserved_231 (ops : ExternalFuns) : (selected ops).op231 = ops.op231 := rfl
theorem preserved_232 (ops : ExternalFuns) : (selected ops).op232 = ops.op232 := rfl
theorem preserved_233 (ops : ExternalFuns) : (selected ops).op233 = ops.op233 := rfl
theorem preserved_234 (ops : ExternalFuns) : (selected ops).op234 = ops.op234 := rfl
theorem preserved_235 (ops : ExternalFuns) : (selected ops).op235 = ops.op235 := rfl
theorem preserved_236 (ops : ExternalFuns) : (selected ops).op236 = ops.op236 := rfl
theorem preserved_237 (ops : ExternalFuns) : (selected ops).op237 = ops.op237 := rfl
theorem preserved_238 (ops : ExternalFuns) : (selected ops).op238 = ops.op238 := rfl
theorem preserved_239 (ops : ExternalFuns) : (selected ops).op239 = ops.op239 := rfl
theorem preserved_240 (ops : ExternalFuns) : (selected ops).op240 = ops.op240 := rfl
theorem preserved_241 (ops : ExternalFuns) : (selected ops).op241 = ops.op241 := rfl
theorem preserved_242 (ops : ExternalFuns) : (selected ops).op242 = ops.op242 := rfl
theorem preserved_243 (ops : ExternalFuns) : (selected ops).op243 = ops.op243 := rfl
theorem preserved_244 (ops : ExternalFuns) : (selected ops).op244 = ops.op244 := rfl
theorem preserved_245 (ops : ExternalFuns) : (selected ops).op245 = ops.op245 := rfl
theorem preserved_246 (ops : ExternalFuns) : (selected ops).op246 = ops.op246 := rfl
theorem preserved_247 (ops : ExternalFuns) : (selected ops).op247 = ops.op247 := rfl
theorem preserved_248 (ops : ExternalFuns) : (selected ops).op248 = ops.op248 := rfl
theorem preserved_249 (ops : ExternalFuns) : (selected ops).op249 = ops.op249 := rfl
theorem preserved_251 (ops : ExternalFuns) : (selected ops).op251 = ops.op251 := rfl
theorem preserved_252 (ops : ExternalFuns) : (selected ops).op252 = ops.op252 := rfl
theorem preserved_253 (ops : ExternalFuns) : (selected ops).op253 = ops.op253 := rfl
theorem preserved_254 (ops : ExternalFuns) : (selected ops).op254 = ops.op254 := rfl
theorem preserved_255 (ops : ExternalFuns) : (selected ops).op255 = ops.op255 := rfl
theorem preserved_256 (ops : ExternalFuns) : (selected ops).op256 = ops.op256 := rfl
theorem preserved_257 (ops : ExternalFuns) : (selected ops).op257 = ops.op257 := rfl
theorem preserved_258 (ops : ExternalFuns) : (selected ops).op258 = ops.op258 := rfl
theorem preserved_259 (ops : ExternalFuns) : (selected ops).op259 = ops.op259 := rfl
theorem preserved_260 (ops : ExternalFuns) : (selected ops).op260 = ops.op260 := rfl
theorem preserved_261 (ops : ExternalFuns) : (selected ops).op261 = ops.op261 := rfl
#print axioms callback
#print axioms selected
#print axioms originalDictionary
#print axioms selected_callback
#print axioms nonfailure
#print axioms value_law
#print axioms nonvacuity
#print axioms dictionaries
#print axioms observations
#print axioms result_observations
#print axioms preserved_0
#print axioms preserved_1
#print axioms preserved_2
#print axioms preserved_3
#print axioms preserved_4
#print axioms preserved_5
#print axioms preserved_6
#print axioms preserved_7
#print axioms preserved_8
#print axioms preserved_9
#print axioms preserved_10
#print axioms preserved_11
#print axioms preserved_12
#print axioms preserved_13
#print axioms preserved_14
#print axioms preserved_15
#print axioms preserved_16
#print axioms preserved_17
#print axioms preserved_18
#print axioms preserved_19
#print axioms preserved_20
#print axioms preserved_21
#print axioms preserved_22
#print axioms preserved_23
#print axioms preserved_24
#print axioms preserved_25
#print axioms preserved_26
#print axioms preserved_27
#print axioms preserved_28
#print axioms preserved_29
#print axioms preserved_30
#print axioms preserved_31
#print axioms preserved_32
#print axioms preserved_33
#print axioms preserved_34
#print axioms preserved_35
#print axioms preserved_36
#print axioms preserved_37
#print axioms preserved_38
#print axioms preserved_39
#print axioms preserved_40
#print axioms preserved_41
#print axioms preserved_42
#print axioms preserved_43
#print axioms preserved_44
#print axioms preserved_45
#print axioms preserved_46
#print axioms preserved_47
#print axioms preserved_48
#print axioms preserved_49
#print axioms preserved_50
#print axioms preserved_51
#print axioms preserved_52
#print axioms preserved_53
#print axioms preserved_54
#print axioms preserved_55
#print axioms preserved_56
#print axioms preserved_57
#print axioms preserved_58
#print axioms preserved_59
#print axioms preserved_60
#print axioms preserved_61
#print axioms preserved_62
#print axioms preserved_63
#print axioms preserved_64
#print axioms preserved_65
#print axioms preserved_66
#print axioms preserved_67
#print axioms preserved_68
#print axioms preserved_69
#print axioms preserved_70
#print axioms preserved_71
#print axioms preserved_72
#print axioms preserved_73
#print axioms preserved_74
#print axioms preserved_75
#print axioms preserved_76
#print axioms preserved_77
#print axioms preserved_78
#print axioms preserved_79
#print axioms preserved_80
#print axioms preserved_81
#print axioms preserved_82
#print axioms preserved_83
#print axioms preserved_84
#print axioms preserved_85
#print axioms preserved_86
#print axioms preserved_87
#print axioms preserved_88
#print axioms preserved_89
#print axioms preserved_90
#print axioms preserved_91
#print axioms preserved_92
#print axioms preserved_93
#print axioms preserved_94
#print axioms preserved_95
#print axioms preserved_96
#print axioms preserved_97
#print axioms preserved_98
#print axioms preserved_99
#print axioms preserved_100
#print axioms preserved_101
#print axioms preserved_102
#print axioms preserved_103
#print axioms preserved_104
#print axioms preserved_105
#print axioms preserved_106
#print axioms preserved_107
#print axioms preserved_108
#print axioms preserved_109
#print axioms preserved_110
#print axioms preserved_111
#print axioms preserved_112
#print axioms preserved_113
#print axioms preserved_114
#print axioms preserved_115
#print axioms preserved_116
#print axioms preserved_117
#print axioms preserved_118
#print axioms preserved_119
#print axioms preserved_120
#print axioms preserved_121
#print axioms preserved_122
#print axioms preserved_123
#print axioms preserved_124
#print axioms preserved_125
#print axioms preserved_126
#print axioms preserved_127
#print axioms preserved_128
#print axioms preserved_129
#print axioms preserved_130
#print axioms preserved_131
#print axioms preserved_132
#print axioms preserved_133
#print axioms preserved_134
#print axioms preserved_135
#print axioms preserved_136
#print axioms preserved_137
#print axioms preserved_138
#print axioms preserved_139
#print axioms preserved_140
#print axioms preserved_141
#print axioms preserved_142
#print axioms preserved_143
#print axioms preserved_144
#print axioms preserved_145
#print axioms preserved_146
#print axioms preserved_147
#print axioms preserved_148
#print axioms preserved_149
#print axioms preserved_150
#print axioms preserved_151
#print axioms preserved_152
#print axioms preserved_153
#print axioms preserved_154
#print axioms preserved_155
#print axioms preserved_156
#print axioms preserved_157
#print axioms preserved_158
#print axioms preserved_159
#print axioms preserved_160
#print axioms preserved_161
#print axioms preserved_162
#print axioms preserved_163
#print axioms preserved_164
#print axioms preserved_165
#print axioms preserved_166
#print axioms preserved_167
#print axioms preserved_168
#print axioms preserved_169
#print axioms preserved_170
#print axioms preserved_171
#print axioms preserved_172
#print axioms preserved_173
#print axioms preserved_174
#print axioms preserved_175
#print axioms preserved_176
#print axioms preserved_177
#print axioms preserved_178
#print axioms preserved_179
#print axioms preserved_180
#print axioms preserved_181
#print axioms preserved_182
#print axioms preserved_183
#print axioms preserved_184
#print axioms preserved_185
#print axioms preserved_186
#print axioms preserved_187
#print axioms preserved_188
#print axioms preserved_189
#print axioms preserved_190
#print axioms preserved_191
#print axioms preserved_192
#print axioms preserved_193
#print axioms preserved_194
#print axioms preserved_195
#print axioms preserved_196
#print axioms preserved_197
#print axioms preserved_198
#print axioms preserved_199
#print axioms preserved_200
#print axioms preserved_201
#print axioms preserved_202
#print axioms preserved_203
#print axioms preserved_204
#print axioms preserved_205
#print axioms preserved_206
#print axioms preserved_207
#print axioms preserved_208
#print axioms preserved_209
#print axioms preserved_210
#print axioms preserved_211
#print axioms preserved_212
#print axioms preserved_213
#print axioms preserved_214
#print axioms preserved_215
#print axioms preserved_216
#print axioms preserved_217
#print axioms preserved_218
#print axioms preserved_219
#print axioms preserved_220
#print axioms preserved_221
#print axioms preserved_222
#print axioms preserved_223
#print axioms preserved_224
#print axioms preserved_225
#print axioms preserved_226
#print axioms preserved_227
#print axioms preserved_228
#print axioms preserved_229
#print axioms preserved_230
#print axioms preserved_231
#print axioms preserved_232
#print axioms preserved_233
#print axioms preserved_234
#print axioms preserved_235
#print axioms preserved_236
#print axioms preserved_237
#print axioms preserved_238
#print axioms preserved_239
#print axioms preserved_240
#print axioms preserved_241
#print axioms preserved_242
#print axioms preserved_243
#print axioms preserved_244
#print axioms preserved_245
#print axioms preserved_246
#print axioms preserved_247
#print axioms preserved_248
#print axioms preserved_249
#print axioms preserved_251
#print axioms preserved_252
#print axioms preserved_253
#print axioms preserved_254
#print axioms preserved_255
#print axioms preserved_256
#print axioms preserved_257
#print axioms preserved_258
#print axioms preserved_259
#print axioms preserved_260
#print axioms preserved_261
end PV_B2_E_Install250
