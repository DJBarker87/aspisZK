import CuSavingsGammaSourceBinding
set_option autoImplicit false
namespace AspisR1.CuSavingsGammaPrefixData
open CuSavingsGammaSourceBinding
-- These two independently obtained token lists are the exact source tails.
def parentTail : List String := ["let","k","=","powers","::","<","7",">","(","kappa",")",";","let","mut","parts","=","[","E","::","ZERO",";","7","]",";","parts","[","0","]","=","inactive",";","for","point","in","0","..","6","{","let","mut","dot","=","crate","::","fast_pairing","::","EbyKDot","::","new","(",")",";","for","l","in","0","..","29","{","let","scalar","=","match","point","{","0","..=","2","=>","sem",".","claims","[","point","]","[","l","]",",","3","=>","sem",".","extra","[","l","]",",","4","=>","sem",".","before_z1","[","l","]",",","_","=>","field","(","y1",",","l",")",".","c0","(",")","}",";","dot",".","push","(","g","[","l","]",",","scalar",")",".","map_err","(","|","_","|","Error","::","Parse",")","?",";","}","parts","[","point","+","1","]","=","dot",".","finish","(",")",";","}","let","mut","claim","=","E","::","ZERO",";","for","i","in","0","..","7","{","crate","::","trace","::","value","(","14",",","i",",","parts","[","i","]",")",";","claim","=","claim",".","add","(","k","[","i","]",".","mul","(","parts","[","i","]",")",")",";","}","crate","::","trace","::","value","(","14",",","7",",","claim",")",";","Ok","(","claim",")"]
def candidateTail : List String := ["let","k","=","powers","::","<","7",">","(","kappa",")",";","let","mut","parts","=","[","E","::","ZERO",";","7","]",";","parts","[","0","]","=","inactive",";","for","point","in","0","..","6","{","let","mut","dot","=","crate","::","fast_pairing","::","EbyKDot","::","new","(",")",";","for","l","in","0","..","29","{","let","scalar","=","match","point","{","0","..=","2","=>","sem",".","claims","[","point","]","[","l","]",",","3","=>","sem",".","extra","[","l","]",",","4","=>","sem",".","before_z1","[","l","]",",","_","=>","field","(","y1",",","l",")",".","c0","(",")","}",";","dot",".","push","(","g","[","l","]",",","scalar",")",".","map_err","(","|","_","|","Error","::","Parse",")","?",";","}","parts","[","point","+","1","]","=","dot",".","finish","(",")",";","}","let","mut","claim","=","E","::","ZERO",";","for","i","in","0","..","7","{","crate","::","trace","::","value","(","14",",","i",",","parts","[","i","]",")",";","claim","=","claim",".","add","(","k","[","i","]",".","mul","(","parts","[","i","]",")",")",";","}","crate","::","trace","::","value","(","14",",","7",",","claim",")",";","Ok","(","claim",")"]
def parentBlock : Block := .powers29 (.tail parentTail)
def candidateBlock : Block := .tail candidateTail

theorem tail_identity : parentTail=candidateTail := by rfl

theorem prefix_identity : parentBlock=.powers29 candidateBlock := by rfl

#print axioms tail_identity
#print axioms prefix_identity
end AspisR1.CuSavingsGammaPrefixData
