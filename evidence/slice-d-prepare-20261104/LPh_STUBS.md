# Lean-discharged powers products

| Native cut/oracle | Paired Lean theorem | Domain and call-site discharge |
| --- | --- | --- |
| NFW_weights::product(local log,left,right), opaque canonical reply | AspisR1.NFW_LPi_TowerValues.wide_mul | Every eight-word operand limb<P. The native generator admits all canonical E; NFW_LPi_PowersSource.one_canonical and NFW_LPi_PowersValue.loop establish canonicality of every next operand. The returned value is substituted by the natural-number mulE specification and canonical output given by wide_mul. |

The oracle records exact same operands and returns an unconstrained canonical record; it does not evaluate multiplication in Kani. It is an opaque call-log cut under ruling(y), not a proof_for_contract or stub_verified claim. The model theorem returns ok with exactly mulE on the domain. K005/K007 prove operand order and caller frame; K006/K008 are matched failing controls. Source fields/pointers and complete effects remain in the root interpretation boundary. Final-iteration proof NFW_PowersFrame.final requires no product domain, because no product call occurs.
