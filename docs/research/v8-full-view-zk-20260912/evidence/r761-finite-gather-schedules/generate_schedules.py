#!/usr/bin/env python3
"""Generate only finite index schedules/sourceGather identities required by the R748 343-pointWeight plan."""
from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent / "generated"
PLAN = ROOT / ".r21-scratch/r748-chosen222-point1-leaf-plan.json"
PLAN_SHA256 = "55f19bf194589ef1229ae6d96ce0d7ef16b1b8d3466b40d00cc0e9fa4b906dd4"
LEAN = ROOT / "docs/research/v8-full-view-zk-20260912/lean"
PINS = {
    ".r21-scratch/r748-chosen222-point1-leaf-plan.json": "",
    "docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/IndexSchedule.lean": "363b0eb4491d3cb40ad5d097e5e7f0242677f43808a1839bafe80add2356cfcf",
    "docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R742SourceObservationHom.lean": "a0a013308a572e3a76cac3c0c168cbe27c9fd274338debb275eb771226182e4b",
    "docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R748FiniteGatherSchedules.lean": "41e1c67ae4476481bcff834dc153d172b97c06c9aff0873ede51d1598eb84e4b",
    ".r21-scratch/r748-gather-schedule-generator/PrototypeDensest255.lean": "1e8086e99dc42e379589a2db7df47bf25859cba0117baa8974e44bdd536ad1fa",
}

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def index_loop(fuel: int, row: int, bit: int = 0):
    if fuel == 0:
        return None
    if row & (1 << bit):
        nxt = row ^ (1 << bit)
        rest = index_loop(fuel - 1, nxt, bit + 1)
        return None if rest is None else [(nxt, bit + 1)] + rest
    return [(row | (1 << bit), bit)]

def lean_edges(edges):
    return "[" + ",".join(f"({r},{e})" for r,e in edges) + "]"

def term(pow_, row):
    return ("half" if pow_ == 1 else f"half^{pow_}") + f"*w {row}"

def chunks(xs, size=32):
    return [xs[i:i+size] for i in range(0, len(xs), size)]

def read_existing():
    src=(LEAN/"AspisV8R19/R748FiniteGatherSchedules.lean").read_text()
    loops=set(map(int,re.findall(r"lemma loop(\d+)\b",src)))
    gathers=set(map(int,re.findall(r"lemma gather(\d+)\s*\(",src)))
    nested=set(map(int,re.findall(r"lemma gatherGather(\d+)\s*\(",src)))
    return src,loops,gathers,nested

def build():
    if sha(PLAN) != PLAN_SHA256:
        raise SystemExit(f"plan pin mismatch: {sha(PLAN)} != {PLAN_SHA256}")
    plan=json.loads(PLAN.read_text())
    indices=plan.get("needed_pointWeight_indices")
    if not isinstance(indices,list) or len(indices)!=343 or len(set(indices))!=343:
        raise SystemExit("plan must contain exactly 343 distinct needed_pointWeight_indices")
    if any(type(i) is not int or i<0 or i>=1024 for i in indices):
        raise SystemExit("pointWeight index out of supported source range")
    outer={i//2 for i in indices}
    nested={i//2 for i in indices if i%2==1}
    schedules=set(outer)
    for i in nested:
        es=index_loop(10,i)
        if es is None: raise SystemExit(f"indexLoop unexpectedly exhausted at {i}")
        schedules.update(r for r,_ in es)
    if not schedules or max(schedules)>=512:
        raise SystemExit("schedule row outside the pinned 512-row source domain")
    schedule={i:index_loop(10,i) for i in sorted(schedules)}
    if any(v is None or len(v)>10 for v in schedule.values()):
        raise SystemExit("invalid ten-fuel schedule")
    source,oldloops,oldgathers,oldnested=read_existing()
    proto_path=Path(__file__).with_name("PrototypeDensest255.lean")
    proto=proto_path.read_text()
    protoloops=set(map(int,re.findall(r"lemma loop(\d+)\b",proto)))
    protogathers=set(map(int,re.findall(r"lemma gather(\d+)\s*\(",proto)))
    protonested=set(map(int,re.findall(r"lemma gatherGather(\d+)\s*\(",proto)))
    newloops=[i for i in sorted(schedules) if i not in oldloops|protoloops]
    newgathers=[i for i in sorted(schedules) if i not in oldgathers|protogathers]
    newnested=[i for i in sorted(nested) if i not in oldnested|protonested]
    all_gathers=oldgathers|protogathers|set(newgathers)
    for i in newnested:
        for r,_ in schedule[i]:
            if r not in all_gathers:
                raise SystemExit(f"nested gather {i} needs ungenerated gather{r}")
    outputs=[]
    prev="AspisV8R19.R748FiniteGatherSchedules"
    def header(name, opened=()):
        opens = "\n".join(f"open {ns}" for ns in opened)
        return (f"import {prev}\nimport AspisV8R19.R748SchedulePrototype\n/-! Generated index-only finite schedule identities for the pinned R748 pointWeight plan. -/\n"
                "set_option autoImplicit false\n"
                f"namespace AspisV8R19.{name}\nopen AspisV8R17\nopen AspisV8R19.R742SourceObservationHom\n"
                "open AspisV8R19.R748FiniteGatherSchedules\nopen AspisV8R19.R748SchedulePrototype\n" + opens + "\n")
    loopfiles=[]
    for ci, part in enumerate(chunks(newloops)):
        name=f"R748GatherLoop{ci:02d}"
        rows=[]
        for i in part:
            es=schedule[i]
            rows.append(f"lemma loop{i} : indexLoop 10 {i} 0 = some {lean_edges(es)} := by rfl\n#print axioms loop{i}\n")
        body=header(name, loopfiles[:-1])+"\n".join(rows)+f"end AspisV8R19.{name}\n"
        filename=f"{name}.lean"; outputs.append((filename,body)); loopfiles.append(f"AspisV8R19.{name}")
        prev=f"AspisV8R19.{name}"
    gatherfiles=[]
    # Ensure all generated gather proofs see every new loop theorem.
    if loopfiles: prev=loopfiles[-1]
    for ci,part in enumerate(chunks(newgathers)):
        name=f"R748GatherExpand{ci:02d}"
        rows=[]
        for i in part:
            es=schedule[i]
            rhs=" + ".join(term(e,r) for r,e in es)
            rows.append(f"lemma gather{i} (half : F) (w : Nat → F) :\n    sourceGather half w {i} = {rhs} := by\n  rw [sourceGather_powers, loop{i}]\n  simp <;> ring\n#print axioms gather{i}\n")
        openloops="\n".join(f"open {ns}" for ns in loopfiles)
        proofdeps="\n".join(f"open {ns}" for ns in gatherfiles)
        opens="\n".join(x for x in (openloops,proofdeps) if x)
        body=(f"import {prev}\n/-! Generated sourceGather expansions from named ten-fuel schedules. -/\n"
              "set_option autoImplicit false\n"
              f"namespace AspisV8R19.{name}\nopen AspisV8R17\nopen AspisV8R19.R742SourceObservationHom\nopen AspisV8R19.R748FiniteGatherSchedules\nopen AspisV8R19.R748SchedulePrototype\n{opens}\n"
              "variable {F : Type*} [CommRing F]\n"+"\n".join(rows)+f"end AspisV8R19.{name}\n")
        filename=f"{name}.lean"; outputs.append((filename,body)); gatherfiles.append(f"AspisV8R19.{name}"); prev=f"AspisV8R19.{name}"
    for ci,part in enumerate(chunks(newnested)):
        name=f"R748GatherNested{ci:02d}"
        rows=[]
        for i in part:
            es=schedule[i]
            childrows=sorted({r for r,_ in es})
            flat=[(leaf,e1+e2) for r,e1 in es for leaf,e2 in schedule[r]]
            rhs=" + ".join(term(e,r) for r,e in flat)
            rwlist=[f"gather{i}"]+[f"gather{r}" for r in childrows]
            rows.append(f"lemma gatherGather{i} (half : F) (w : Nat → F) :\n    sourceGather half (sourceGather half w) {i} = {rhs} := by\n  rw [{', '.join(rwlist)}] <;> simp <;> ring\n#print axioms gatherGather{i}\n")
        allopens="\n".join(f"open {ns}" for ns in (loopfiles+gatherfiles+gatherfiles[:ci]))
        body=(f"import {prev}\n/-! Generated nested sourceGather expansions for odd pointWeight indices. -/\n"
              "set_option autoImplicit false\n"
              f"namespace AspisV8R19.{name}\nopen AspisV8R17\nopen AspisV8R19.R742SourceObservationHom\nopen AspisV8R19.R748FiniteGatherSchedules\nopen AspisV8R19.R748SchedulePrototype\n{allopens}\n"
              "variable {F : Type*} [CommRing F]\n"+"\n".join(rows)+f"end AspisV8R19.{name}\n")
        filename=f"{name}.lean"; outputs.append((filename,body)); prev=f"AspisV8R19.{name}"
    manifest={"schema":"r748-finite-gather-schedules-v1","plan_sha256":sha(PLAN),"source_sha256":{},"counts":{"pointWeight_indices":len(indices),"outer_rows":len(outer),"nested_outer_rows":len(nested),"distinct_schedules":len(schedules),"new_loop":len(newloops),"new_gather":len(newgathers),"new_gatherGather":len(newnested),"max_schedule_edges":max(map(len,schedule.values())),"max_row":max(schedules)},"rows":{"outer":sorted(outer),"nested_outer":sorted(nested),"all_schedule":sorted(schedules),"new_loop":newloops,"new_gather":newgathers,"new_gatherGather":newnested},"existing":{"loop":sorted(oldloops),"gather":sorted(oldgathers),"gatherGather":sorted(oldnested)},"reused_prototype":{"loop":sorted(protoloops),"gather":sorted(protogathers),"gatherGather":sorted(protonested)},"chunk_declarations":{filename:len(re.findall(r"^lemma ",body,re.M)) for filename,body in outputs},"outputs":{}}
    if any(count>32 for count in manifest["chunk_declarations"].values()):
        raise SystemExit("generated declaration chunk exceeds 32")
    for rel in list(PINS)[1:]:
        p=ROOT/rel; actual=sha(p); expected=PINS[rel]
        if actual!=expected: raise SystemExit(f"source pin mismatch: {rel}: {actual} != {expected}")
        manifest["source_sha256"][rel]=actual
    for filename,body in outputs: manifest["outputs"][filename]=hashlib.sha256(body.encode()).hexdigest()
    return outputs,manifest

def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--check",action="store_true"); args=ap.parse_args()
    outputs,manifest=build()
    manifest_text=json.dumps(manifest,indent=2,sort_keys=True)+"\n"
    OUT.mkdir(parents=True,exist_ok=True)
    stale=[]
    expected_lean={filename for filename,_ in outputs}
    actual_lean={p.name for p in OUT.glob("*.lean")}
    extras=sorted(actual_lean-expected_lean)
    missing=sorted(expected_lean-actual_lean)
    if args.check and (extras or missing):
        stale.append(f"Lean inventory extras={extras} missing={missing}")
    for filename,body in outputs:
        path=OUT/filename
        if args.check:
            if not path.exists() or path.read_text()!=body: stale.append(str(path.relative_to(ROOT)))
        else: path.write_text(body)
    mpath=OUT/"manifest.json"
    if args.check:
        if not mpath.exists() or mpath.read_text()!=manifest_text: stale.append(str(mpath.relative_to(ROOT)))
        if stale: raise SystemExit("generated outputs stale/missing: "+", ".join(stale))
        print("--check: generated outputs and pinned inputs match")
    else:
        mpath.write_text(manifest_text)
        print(json.dumps(manifest["counts"],sort_keys=True))
        print(f"wrote {len(outputs)} Lean files to {OUT}")
if __name__=="__main__": main()
