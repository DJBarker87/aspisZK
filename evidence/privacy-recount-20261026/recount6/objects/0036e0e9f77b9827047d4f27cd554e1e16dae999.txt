# Remaining requested deliverables

2. **Actual-invocation exclusion:** not proved. The seven unchanged whole-caller
replacement equations are reused, not replayed. Their support complement is
{op13,op16,op17,op18,op85,op124,op238}. The missing side of
NoCatchCore.exclusion_by_poisoning is a finite actual invocation-prefix witness
transported to the poisoned execution, including all recursive/higher-order
call boundaries. Local branch/context proofs do not instantiate it. No arbitrary
Prop named invoked is presented as actual invocation. This is an open V404/V405
obligation, not a newly assumed premise.

3. **Native success / minimal reached sets:** not proved. The inherited
ShapePoison.success_distinguishes is conditional on outer success and establishes
op233 necessity at Result level. It is not a native success witness. Neither
S_transfer nor S_withdrawal has been established. U, the inherited 255-field
Result support, is neither reached nor minimal. No entry of U is dropped or
credited merely from its static occurrence.

4. **Exact native hypotheses:** the exact types in ../native-boundary.md are
retained: compile_call : ∀ withdrawal,
  @PV_Src_NativeInput.run external records (inputs withdrawal) =
    Aeneas.Std.Result.ok (.Ok (inputs withdrawal).compiled),
PublicDeploymentAssociation.Association records inputs,
ExternalAssociation.Associated external, and
RecordAssociation.Associated external records.
At the two fixture points the pending compiler instances are exactly
compile_call false and compile_call true; these follow only *if compile_call is
supplied*. The input families/dictionaries and native success are not constructed
here. No conditional equation with an uninhabited antecedent is counted as a
witness. Non-vacuity remains unchecked/open for both inputs and all associations.
No native-association proof was duplicated or assumed as a trust field.

5. **Row comparison:** current research ROWS5 and recount5/rows5.json were read
read-only; row-definitions.json preserves both entire records. They require
complete actual reached sets and all-admitted-input exclusions. The checked
context/entropy/scalar facts do not meet those conditions. V404 OPEN → OPEN;
V405 OPEN → OPEN. Universally excluded callbacks: none proved. No endpoint or
deployment premise was changed, removed, added, or weakened. V163/V167 and the
capped three-field T are unchanged. These unresolved steps are not described as
completed by a collection of local lemmas.
