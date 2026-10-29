# D493 / ruling (v): correction of the two false direct instances

Entry: bb12e1b99e63ca6e18a3cb75b646ee8ab159258a. No release/source/endpoint premise was changed. Earlier counterexamples remain valid and are retained in resume13/FINDINGS.md. They are not op227 counterexamples.

## Zero-mask helper

Before, the direct native instance attempted:

`source_mask11 = reference_copy_terminal.selector_mask_sum_16`.

This is false: source mask zero returns `.ok ZERO`; the seven-case owned helper returns `.fail .panic`.

After, `PV_B3P_Correct14227.PV_B3P_Link_mask_on_domain source` states:

`∀ values mask, MaskAllowed mask → source values mask = reference_copy_terminal.selector_mask_sum_16 values mask`.

The added obligation `PV_B3P_Link_mask_call_domain called` states `∀ mask, called mask → MaskAllowed mask`. The actual table/zero guard is represented by `frozen_calls14 mask := mask ∈ ACTIVE_ROW_MASKS.val ∧ mask ≠ 0`. Both corrected links are jointly satisfied by `source_mask11` and `frozen_calls14` (`mask_joint_witness14`); `mask_at_actual_call14` composes them. The contextual adapter from resume13 remains valid. No unrestricted native equality is claimed.

## Legacy 49-block constructor

Before, the direct instance attempted:

`legacy49_constructor = selector_reference13`.

The target constructor sums 57 high-selector entries; the legacy body sums 49. Boolean coordinate 50 distinguishes them.

After, `PV_B3P_Link_constructor_on_layout source` states:

`∀ blocks, blocks = 57#usize → source blocks = selector_reference13`.

The added `PV_B3P_Link_constructor_call_layout blocks` is `blocks = 57#usize`, a constructor-selection obligation, never a restriction on arbitrary input points. The separately retained `PV_B3P_Link_constructor_native native source blocks` is `native = source blocks`. `constructor_at_call14` composes all three to the old target link. The model `constructor14` expands the same high/low selectors and sums exactly `0..blocks`. `constructor_joint_witness14` jointly instantiates all links at 57. It makes no false claim about the legacy constructor. Native caller selection and source association remain obligations.

## Composition

`CorrectedLinks14` replaces only these two false direct native instances, retains all other 34 function predicates, and exposes both added caller obligations and constructor source association as separate fields. `corrected_links_witness14` and `corrected_callback_joint_witness14` give joint model instances. `selected_callback14` still follows through the previously compiled `selected_callback13` using the unchanged composition/equality links. Its terminal is `transported_reference base` on `Install227.Types base`.

The all-group theorem is a typed conditional schema, including roots, 36 corrected function links, D188 stores, matrix stores, slice iteration and a typed std/dependency family. The complete deployed source-cone family has not yet been instantiated. A model witness does not discharge native interpretation.
