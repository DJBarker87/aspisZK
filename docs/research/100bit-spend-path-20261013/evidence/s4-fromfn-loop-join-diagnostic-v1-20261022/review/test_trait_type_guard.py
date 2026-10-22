#!/usr/bin/env python3
"""Adversarial contract tests for the scoped Aeneas TTraitType join case.

This is a small independent model of the guard, not an execution of the OCaml
matcher. `phys_eq` is modeled as physical-equality fast path followed by
structural equality, matching Aeneas' `Utils.phys_eq` implementation.
"""

from dataclasses import dataclass


REGION = "region"


@dataclass(frozen=True)
class TraitRef:
    # Includes the instantiated clause/reference and its actual generic args.
    clause: object
    trait: object
    args: tuple = ()


@dataclass(frozen=True)
class Projection:
    constructor: str
    trait_ref: TraitRef
    assoc_item: object
    # Generic parameters of the associated type itself (e.g. GAT args).
    assoc_args: tuple = ()


@dataclass(frozen=True)
class DynTrait:
    # Represents nested generics carried under TDynTrait in the LLBC type AST.
    args: tuple


def has_region(value):
    if value == REGION:
        return True
    if isinstance(value, (tuple, list)):
        return any(has_region(x) for x in value)
    if isinstance(value, dict):
        return any(has_region(k) or has_region(v) for k, v in value.items())
    if hasattr(value, "__dataclass_fields__"):
        return any(has_region(getattr(value, name)) for name in value.__dataclass_fields__)
    return False


def config_sensitive_has_region(value):
    """Model the old visitor mode that intentionally skips dyn internals."""
    if isinstance(value, DynTrait):
        return False
    if value == REGION:
        return True
    if isinstance(value, (tuple, list)):
        return any(config_sensitive_has_region(x) for x in value)
    if isinstance(value, dict):
        return any(config_sensitive_has_region(k) or config_sensitive_has_region(v) for k, v in value.items())
    if hasattr(value, "__dataclass_fields__"):
        return any(config_sensitive_has_region(getattr(value, name)) for name in value.__dataclass_fields__)
    return False


def accepts(left, right):
    # This exactly models the branch predicates; the constructor check models
    # matching the TTraitType/TTraitType pattern before the guard is evaluated.
    return (
        isinstance(left, Projection)
        and isinstance(right, Projection)
        and left.constructor == right.constructor == "TTraitType"
        and left == right  # Utils.phys_eq: physical fast path OR structural equality.
        and not has_region(left)
        and not has_region(right)
    )


def main():
    base = Projection("TTraitType", TraitRef(("ParentClause", 0), "Residual", ("Self", ("Output", 3))), "TryType")
    separately_allocated_same = Projection("TTraitType", TraitRef(("ParentClause", 0), "Residual", ("Self", ("Output", 3))), "TryType")
    assert base is not separately_allocated_same
    assert accepts(base, separately_allocated_same), "phys_eq includes structural equality"

    # Same associated item, but a different parent clause or trait args is not
    # the same instantiated projection.
    assert not accepts(base, Projection("TTraitType", TraitRef(("ParentClause", 1), "Residual", ("Self", ("Output", 3))), "TryType"))
    assert not accepts(base, Projection("TTraitType", TraitRef(("ParentClause", 0), "Residual", ("Self", ("Output", 4))), "TryType"))

    # Different associated item; same trait/clause.
    assert not accepts(base, Projection("TTraitType", base.trait_ref, "OtherItem"))

    # Associated-type generic arguments (GAT args) participate in equality.
    gat0 = Projection("TTraitType", base.trait_ref, "Assoc", ("TypeArg", 3))
    gat1 = Projection("TTraitType", base.trait_ref, "Assoc", ("TypeArg", 4))
    assert not accepts(gat0, gat1)

    # A region anywhere in the same physical/structural type rejects the case,
    # including nested trait-reference args and associated GAT args.
    with_ref_region = Projection("TTraitType", TraitRef(("ParentClause", 0), "Residual", (("Nested", REGION),)), "TryType")
    assert with_ref_region is with_ref_region
    assert not accepts(with_ref_region, with_ref_region)
    with_gat_region = Projection("TTraitType", base.trait_ref, "Assoc", ("GAT", REGION))
    assert not accepts(with_gat_region, with_gat_region)

    # A region under dyn-trait internals is missed by the old config-sensitive
    # visitor but found by the strict v3 visitor contract. This models the
    # guard condition only; it does not execute the OCaml visitor.
    with_dyn_region = Projection("TTraitType", TraitRef(("ParentClause", 0), "Residual", (DynTrait((REGION,)),)), "TryType")
    assert not config_sensitive_has_region(with_dyn_region)
    assert has_region(with_dyn_region)
    assert not accepts(with_dyn_region, with_dyn_region)

    # The special case must not intercept another constructor.
    assert not accepts(("TVar", 0), ("TVar", 0))
    print("TTraitType guard contract: structural positives and clause/item/args/region/dyn/constructor negatives PASS")


if __name__ == "__main__":
    main()
