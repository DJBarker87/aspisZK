#!/usr/bin/env python3
"""Render reviewed atomic-law correspondence; this is not a proof checker.

The correspondence judgments below keep different guards/witness domains
separate. Lean receipts establish the theorem and the derived source facts.
"""
from pathlib import Path
from collections import Counter
import copy, hashlib, json, sys

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
BASE = ROOT / "evidence/recount2-20261026/Rc2_premises.json"
old = json.loads(BASE.read_text())
rows = copy.deepcopy(old["rows"])
removed = {
    "L157": "F3X_Join.accepted_raw_join_or_collision derives the accepted source/model join OR the EXACT charged account event; F3X_Bound consumes it.",
    "N117": "The independent old account adversary prefix budget is replaced by the SAME ByteProver account; F3X_AccountMass.budget derives its budget from L154.",
    "N118": "The independent old chooseSecond budget is absent: the adopted byte-source/account construction is bounded from L154, with all rejected prefixes retained.",
    "L182": "Deployment alias of L157; no second removal credit.",
}
for row in rows:
    if row["id"] in removed:
        row.update(status="removed", disposition=removed[row["id"]])
    else:
        row["status"] = "retained"
        row["evidence"] = "F3X_LedgerHeadline kernel statement; unchanged Rc2 field inventory; F3X_Native preserves the SAME native witnesses and continuations"
    if row["id"] == "L159":
        row["disposition"] = "RETAINED with owner-approved frozen3 RunView/semantic/physical carrier. Not equated to or discharged from the old frozen2 carrier."
    if row["id"] in {"L094", "L095", "L096", "L180"}:
        row["disposition"] = "RETAINED in the old native continuation domains. The additional RuntimePersistence/game route is explicit and separately counted; it does not erase these antecedents."

# These global source laws are NOT silently deduplicated with the native
# continuation leaves L133-L148: their quantified witness/guard domains differ.
# Claim and alpha0/1 are PROVED from the SAME authenticated reader fields.
global_ids = [f"L{i:03d}" for i in range(133, 149) if i not in {139, 140, 141}]
by_id = {r["id"]: r for r in old["rows"]}
for ident in global_ids:
    prior = by_id[ident]
    rows.append(dict(
        id="F3X_G_"+ident, name="finishOwners.source_global."+prior["name"],
        classification="P", owner=prior["owner"], scope="actual antecedent", status="added",
        definition="lean/F3X_PreparedAt.lean#Owners; lean/F3X_FinishLeaves.lean",
        meaning=prior["meaning"],
        disposition="Global family over actual source Evidence, source-bound At operands and SAME reached finish primitives. Distinct from the retained local native continuation family; no domain-equivalence premise removal is credited.",
        evidence="F3X_Aligned.values / F3X_Canonical.accepted / F3X_FinishLeaves.complete; kernel field catalog"))

# The key-law equality has literally the same fixed dictionary/type as
# Rc2_P001 and is deduplicated there. Bank positivity is retained separately:
# its initial/source-entry guards differ from the old protection corollary.
history = [
    ("entry1", "P", "e1 is the entry loaded from the SAME initial bank and layout"),
    ("positive", "P", "the SAME initial checkpoint account has positive lamports"),
    ("RuntimePersistence", "T", "CPR_DataPersistence.TwoTransactionLaw; owner approved 2026-10-26"),
    ("adjacent", "P", "TX1/TX2 are consecutive on the selected bank lineage"),
    ("eligible", "P", "the selected physical checkpoint is an ordinary account"),
    ("tentativeView", "P", "tentative physical bytes/lamports are the SAME source-bank final snapshot"),
    ("status", "P", "TX1 final parent status is success"),
    ("entry2View", "P", "the SAME physical key's next loaded data is the actual TX2 checkpoint input"),
]
for name, kind, meaning in history:
    rows.append(dict(id="F3X_H_"+name, name="history.game."+name,
        classification=kind, owner="external" if kind=="T" else "lead",
        scope="actual antecedent", status="added",
        definition="lean/F3X_Result.lean#Outcome; lean/Rc2_History.lean#Facts",
        meaning=meaning, disposition="Guard of the additional SAME-cut history result. Does not gate the basic numerical bound, which still retains L159.",
        evidence="F3X_Native.accepted / F3X_FixtureHistory.binding; kernel history catalog"))

retained = [r for r in rows if r["status"] != "removed"]
def count(rs):
    return {"rows":len(rs), "classes":dict(Counter(r["classification"] for r in rs)),
            "owners":dict(Counter(r["owner"] for r in rs))}
actual = [r for r in retained if r["scope"] == "actual antecedent"]
deploy = [r for r in retained if r["scope"] == "deployment only"]
aliases = [r for r in retained if r["scope"] == "deployment alias"]
counts = {"actual antecedent":count(actual), "deployment only":count(deploy),
          "deployment alias":count(aliases), "all retained audit rows":count(retained),
          "deduplicated actual plus non-alias deployment":count(actual+deploy)}
assert counts["actual antecedent"]["classes"] == {"T":83,"P":188}, counts
assert counts["deduplicated actual plus non-alias deployment"]["classes"] == {"T":89,"P":201}, counts

audit = OUT / sys.argv[1] / "stdout.log" if len(sys.argv)>1 else None
result = dict(actual_theorem="AspisR1.F3X_Headline.deployed",
    baseline=str(BASE.relative_to(ROOT)), baseline_sha256=hashlib.sha256(BASE.read_bytes()).hexdigest(),
    baseline_theorem=old["actual_theorem"], baseline_counts=old["counts"], counts=counts,
    method="Atomic conjunctive leaves and quantified law families; SAME guards/witnesses; shared-dictionary alias deduplication. Reviewed correspondence, not an automatic discharge proof.",
    statement_receipt=str(audit.relative_to(ROOT)) if audit else None,
    statement_sha256=hashlib.sha256(audit.read_bytes()).hexdigest() if audit else None,
    source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/"lean").glob("F3X_*.lean"))},
    removed_actual=["L157","N117","N118"], removed_alias=["L182"],
    derived_source_global=["claim","alpha0","alpha1"],
    deduplicated_history={"keyLaw":"Rc2_P001"}, rows=rows,
    limitations=["Source-global finish laws are explicit NEW scoped law families, not silently equated to native continuation leaves.",
      "L159 uses the owner-approved frozen3 carrier; source/runtime/ELF association remains retained.",
      "L094-L096 remain in the legacy native continuation domains.",
      "The composed fixture is conditional on retained owner/trust laws, accepted native observations and explicit snapshot/load constraints; it is not an unconditional existential model of every release premise."])
(OUT/"F3X_premises.json").write_text(json.dumps(result,indent=2)+"\n")
lines=["# Recount of F3X_Headline.deployed", "", "Target not yet established unconditionally. This is the reviewed atomic-family ledger, not a security percentage.", "", "| Scope | Before T/P | After T/P | Delta T/P |", "|---|---:|---:|---:|", "| Actual antecedents, including application guards | 82 / 171 | 83 / 188 | +1 / +17 |", "| Deduplicated actual plus non-alias deployment | 88 / 184 | 89 / 201 | +1 / +17 |", "", "Removed actual rows: L157, N117, N118. L182 is an alias, with no extra credit. Added: 13 source-global finish families and 7 game/association guards plus RuntimePersistence. The source-global claim/alpha0/alpha1 families are proved from the actual reader; their old native-continuation rows remain. Key-law alias is Rc2_P001. No structure/binder count subtraction.", "", "The total increases because different source-global and native-local guard domains are kept separate, and the new history route's guards are exposed. This is not a claim of a net reduction in atomic premise count.", "", "Full kernel statements/definitions and before/after source hashes are pinned in F3X_premises.json. All native witnesses remain shared. The runtime item and two-entry source-bank fixture are model/trust composition, not a fresh source-to-ELF validation. See F3X_STAGE2-4 and the final handoff for exact scope.", "", "| ID | Name | Class / owner | Status / scope | Disposition |", "|---|---|---|---|---|"]
for r in rows:
    lines.append(f"| {r['id']} | {r['name']} | {r['classification']} / {r['owner']} | {r['status']} / {r['scope']} | {r.get('disposition','Retained with the same atomic meaning; see baseline field inventory.')} |")
(OUT/"F3X_LEDGER.md").write_text("\n".join(lines)+"\n")
print(json.dumps(counts,indent=2))
