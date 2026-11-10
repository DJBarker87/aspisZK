#!/usr/bin/env python3
"""NPO_ v2 generator for NPO_FinalB.lean (corrects the three v1 defects recorded for NPO_L018):
 (1) NNH8_RecorderFixed.fixedProgram is a re-instantiated constant and is renamed like the others;
 (2) TAS_FinalB's open order is kept: the AspisV8R19/FS opens precede deployed_charge only;
 (3) ctx_same is dropped.
Adds the short alias names NPO_Program.verifier, NPO_Instances.D, NPO_Run5bHost.S_host and
NPO_FinalB.{deployed_splitB,deployed_charge,fail_sub_rec,deployed_outer} (10 November instance),
with the 29 October instance under the same names suffixed Oct.
Usage: NPO_gen_final2.py <TAS_FinalB.lean> > NPO_FinalB.lean"""
import sys, re
src = open(sys.argv[1]).read()
OPENS1 = ("open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers\n"
          "open RSL RSL.TAS RSL.TASB NNH_Libraries\nopen NNH_Run6Installed\nvariable {W Tx : Type}\n")
OPENS2 = "open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep\nopen AspisV8R19.MemoizedProgramLaw\nopen FS FS2\n"
assert OPENS1.split("variable")[0] in src and OPENS2 in src
run7 = src[src.index("/-! Run 7 (G0 FINAL)"):src.index("/-! Delivered-type checks")]
CLONED = ["NOC_Run5bHost.S_host", "NOC_Run5bHost.runtime", "NNH8_Exec.exec", "NNH8_Split.rest",
          "NNH8_HeadlineB.headlineB", "NNH8_RecorderFixed.fixedProgram"]
def stmts(P):
    out = {}
    for m in re.finditer(r"theorem (deployed_splitB|fail_sub_rec|deployed_charge)\n(.*?) :=( by\n exact|\n) ", run7, re.S):
        name, body = m.group(1), m.group(2)
        for c in CLONED: body = re.sub(r"(?<![\w.])" + re.escape(c), f"{P}.AspisR1.{c}", body)
        body = body.replace("(implementation ", f"({P}.AspisR1.NNH_Run6Installed.implementation ")
        names = " ".join(n for line in body.split("\n") if line.startswith(" (")
                         for grp in re.findall(r"\((\w+(?: \w+)*) :(?!=)", line) for n in grp.split())
        out[name] = f"theorem {name}\n{body} :=\n {P}.AspisR1.TAS_FinalB.{name} {names}\n"
    return out
def block(inst, sfx):
    P = f"NPO_{inst}"; s = stmts(P)
    D_extra = "/-- The 29 October D is the pinned LIB_Deployed.devnet. -/\ntheorem D_devnet : D = LIB_Deployed.devnet := rfl\n" if inst == "Oct" else ""
    return f"""namespace NPO_Program{sfx}
/-- CPH_Program.verifier with the id replaced ({inst} deployment). -/
abbrev verifier : AspisR1.S2W_ExtractionBoundary.Program := NPO_DeployedIds.verifier{inst}
end NPO_Program{sfx}
namespace NPO_Instances{sfx}
/-- LIB_Instances.D with the Pool/registry program ids replaced (kernel-checked copy). -/
abbrev D : RSL.DeployedIds := {P}.LIB_Instances.D
theorem D_eq : D = NPO_DeployedIds.D{inst} := rfl
{D_extra}end NPO_Instances{sfx}
namespace NPO_Run5bHost{sfx}
/-- NOC_Run5bHost.S_host, same construction, at the {inst} ids (kernel-checked copy). -/
abbrev S_host := @{P}.AspisR1.NOC_Run5bHost.S_host
end NPO_Run5bHost{sfx}
namespace AspisR1.NPO_Run5bHostChecks{sfx}
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open RSL RSL.TAS RSL.TASB NNH_Libraries
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.MemoizedProgramLaw
variable {{W Tx : Type}}
theorem type_same : type_of% @NPO_Run5bHost{sfx}.S_host = type_of% @AspisR1.NOC_Run5bHost.S_host := rfl
theorem args1_at (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) (c : NOC_Run5bCtx.Ctx W Tx) :
 (NPO_Run5bHost{sfx}.S_host (Tx := Tx) L copy std).args1 c = NNE_EntryArgs.args c.i.entry 3 NPO_Program{sfx}.verifier c.i.data := rfl
theorem args2_at (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy) (c : NOC_Run5bCtx.Ctx W Tx) :
 (NPO_Run5bHost{sfx}.S_host (Tx := Tx) L copy std).args2 c = NNE_EntryArgs.args c.j.entry 7 NPO_Program{sfx}.verifier c.j.data := rfl
end AspisR1.NPO_Run5bHostChecks{sfx}
namespace AspisR1.NPO_FinalB{sfx}
{OPENS1}
{s['deployed_splitB']}
{s['fail_sub_rec']}
{OPENS2}
{s['deployed_charge']}end AspisR1.NPO_FinalB{sfx}
namespace NPO_FinalB{sfx}
theorem deployed_splitB : type_of% @AspisR1.NPO_FinalB{sfx}.deployed_splitB := @AspisR1.NPO_FinalB{sfx}.deployed_splitB
theorem deployed_charge : type_of% @AspisR1.NPO_FinalB{sfx}.deployed_charge := @AspisR1.NPO_FinalB{sfx}.deployed_charge
theorem fail_sub_rec : type_of% @AspisR1.NPO_FinalB{sfx}.fail_sub_rec := @AspisR1.NPO_FinalB{sfx}.fail_sub_rec
theorem deployed_outer : type_of% @{P}.AspisR1.NNH8_DeployedOuter := @{P}.AspisR1.NNH8_DeployedOuter
end NPO_FinalB{sfx}
"""
hdr = """import NPO_CloneNov
import NPO_CloneOct
/-! NPO_FinalB (v2): the run-7 top theorems of TAS_FinalB at the host re-instantiated at the deployed
program ids. Short names = 10 November 2026 devnet deployment (verifier GqZzWuGT, Pool 37hdATMk,
registry program 9pWwAcBg); names suffixed Oct = 29 October 2026 (verifier CSnhzGdH, Pool BmsNikL9,
registry program 9pWwAcBg). Statements are TAS_FinalB's run-7 text with the re-instantiated host
constants named NPO_<Inst>.*; proofs are the kernel-checked copies (NPO_L015/L016, replayed by
leanchecker in NPO_L026/L027). Generated by NPO_gen_final2.py. -/
set_option autoImplicit false
noncomputable section
"""
out = hdr + block("Nov", "") + block("Oct", "Oct") + "end\n"
for sfx, inst in (("", "Nov"), ("Oct", "Oct")):
    for t in ([f"NPO_DeployedIds.not_system{inst}", f"NPO_Instances{sfx}.D_eq"] + ([f"NPO_Instances{sfx}.D_devnet"] if sfx else [])
              + [f"AspisR1.NPO_Run5bHostChecks{sfx}.{x}" for x in ("type_same", "args1_at", "args2_at")]
              + [f"AspisR1.NPO_FinalB{sfx}.{x}" for x in ("deployed_splitB", "fail_sub_rec", "deployed_charge")]
              + [f"NPO_FinalB{sfx}.{x}" for x in ("deployed_splitB", "deployed_charge", "fail_sub_rec", "deployed_outer")]):
        out += f"#print axioms {t}\n"
sys.stdout.write(out)
