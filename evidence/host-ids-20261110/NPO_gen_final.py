#!/usr/bin/env python3
"""NPO_: generate NPO_FinalB<Inst>.lean from TAS_FinalB's run-7 statements with the host replaced.
Substitutions (textual, statement side only): every cloned constant C used in the statements is
written NPO_<Inst>.C; nothing else changes. Proofs are the kernel-checked clones."""
import sys, re
inst = sys.argv[1]; P = f"NPO_{inst}"
src = open(sys.argv[2]).read()
run7 = src[src.index("namespace AspisR1.TAS_FinalB\nopen Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers\nopen RSL RSL.TAS RSL.TASB NNH_Libraries\nopen NNH_Run6Installed"):]
run7 = run7[:run7.index("/-! Delivered-type checks")]
# cloned constants that occur in the statements (from the clone log)
ren = {"NOC_Run5bHost.S_host": f"{P}.AspisR1.NOC_Run5bHost.S_host",
       "NOC_Run5bHost.runtime": f"{P}.AspisR1.NOC_Run5bHost.runtime",
       "NNH8_Exec.exec": f"{P}.AspisR1.NNH8_Exec.exec",
       "NNH8_Split.rest": f"{P}.AspisR1.NNH8_Split.rest",
       "NNH8_HeadlineB.headlineB": f"{P}.AspisR1.NNH8_HeadlineB.headlineB",
       "(implementation ": f"({P}.AspisR1.NNH_Run6Installed.implementation ",
       "NNH8_RecorderFixed.fixedProgram": "AspisR1.NNH8_RecorderFixed.fixedProgram"}
stm = []
for m in re.finditer(r"theorem (deployed_splitB|fail_sub_rec|deployed_charge)\n(.*?) :=( by\n exact|\n) ", run7, re.S):
    name, body = m.group(1), m.group(2)
    for a, b in ren.items(): body = body.replace(a, b)
    names = " ".join(n for line in body.split("\n") if line.startswith(" (")
                     for grp in re.findall(r"\((\w+(?: \w+)*) :(?!=)", line) for n in grp.split())
    stm.append(f"theorem {name}\n{body} :=\n {P}.AspisR1.TAS_FinalB.{name} {names}\n")
extraD = "/-- The 29 October D is the already-pinned LIB_Deployed.devnet. -/\ntheorem D_devnet : D = LIB_Deployed.devnet := rfl\n" if inst == "Oct" else ""
hdr = f"""import NPO_Clone{inst}
set_option autoImplicit false
noncomputable section
namespace NPO_Program{inst}
open Aeneas Aeneas.Std
/-- CPH_Program.verifier with the id replaced by the {inst} deployment's verifier id. -/
abbrev verifier : AspisR1.S2W_ExtractionBoundary.Program := NPO_DeployedIds.verifier{inst}
end NPO_Program{inst}
namespace NPO_Instances{inst}
/-- LIB_Instances.D with the Pool/registry ids replaced (the kernel-checked clone). -/
abbrev D : RSL.DeployedIds := {P}.LIB_Instances.D
theorem D_eq : D = NPO_DeployedIds.D{inst} := rfl
{extraD}end NPO_Instances{inst}
namespace AspisR1.NPO_Run5bHost{inst}
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw
variable {{W Tx : Type}}
/-- NOC_Run5bHost.S_host built by the same construction at the {inst} ids. -/
abbrev S_host := @{P}.AspisR1.NOC_Run5bHost.S_host
theorem type_same : type_of% @S_host = type_of% @AspisR1.NOC_Run5bHost.S_host := rfl
theorem ctx_same (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) :
 (S_host (Tx := Tx) L copy std).Ctx = (AspisR1.NOC_Run5bHost.S_host (Tx := Tx) L copy std).Ctx := rfl
theorem args1_at (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) (c : NOC_Run5bCtx.Ctx W Tx) :
 (S_host (Tx := Tx) L copy std).args1 c = NNE_EntryArgs.args c.i.entry 3 NPO_Program{inst}.verifier c.i.data := rfl
theorem args2_at (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) (c : NOC_Run5bCtx.Ctx W Tx) :
 (S_host (Tx := Tx) L copy std).args2 c = NNE_EntryArgs.args c.j.entry 7 NPO_Program{inst}.verifier c.j.data := rfl
end AspisR1.NPO_Run5bHost{inst}
"""
body = run7.split("\n",1)[0].replace("AspisR1.TAS_FinalB", f"AspisR1.NPO_FinalB{inst}") + "\n" + run7.split("\n",1)[1]
opens = body[:body.index("theorem deployed_splitB")].replace("variable {W Tx : Type}",
  "open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep\nopen AspisV8R19.MemoizedProgramLaw\nopen FS FS2\nvariable {W Tx : Type}")
out = hdr + opens + "\n".join(stm) + f"end AspisR1.NPO_FinalB{inst}\nend\n"
for t in ["NPO_DeployedIds.not_system"+inst, f"NPO_Instances{inst}.D_eq", ] + ([f"NPO_Instances{inst}.D_devnet"] if inst=="Oct" else []) + [f"AspisR1.NPO_Run5bHost{inst}.type_same",
          f"AspisR1.NPO_Run5bHost{inst}.ctx_same", f"AspisR1.NPO_Run5bHost{inst}.args1_at", f"AspisR1.NPO_Run5bHost{inst}.args2_at",
          f"AspisR1.NPO_FinalB{inst}.deployed_splitB", f"AspisR1.NPO_FinalB{inst}.fail_sub_rec", f"AspisR1.NPO_FinalB{inst}.deployed_charge"]:
    out += f"#print axioms {t}\n"
open(f"NPO_FinalB{inst}.lean","w").write(out)
