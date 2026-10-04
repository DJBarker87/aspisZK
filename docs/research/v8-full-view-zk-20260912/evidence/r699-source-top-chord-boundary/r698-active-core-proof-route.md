# Lead route: actual active H1 core nonvanishing (UNPROVED)

Authoritative parent74f4cc151. Goal stays full privacy/security; this route is one missing active-H1 component, not a sufficient simulator.

Correct TwoSwap source order gives214 active code positions:213 in blocks d22..254, plus1022. Each high block has at most3 selected slots. At alpha1 and scalar chord(a,b,c)=(2,0,0), high213 rows have an explicit invertible minor: for every active nonzero slot select that channel; for an active slot0 select an unused nonconstant channel. The slot0 row is minus the sum, the remaining rows are identity. This requires exact finite table/source model binding, not merely the inventory. Blocks254 active slots1/3 leave channel2 (q1018) unused. Add that column; scalar214 minor has rank213, not214. Do not claim scalar witness closes it.

Index-only source schedule inspection (r697-top-scatter-shape.json) gives X at511=input510; XX*X at511=half*(input509+input511). Therefore with q1020..1023 allzero, actual source-shaped code1022=-c*half*q1019 when b0; code1019=c*q1018+a*q1019. For a2, replacing top row by top+(c*half/2)*row1019 yields(c^2*half/2)*q1018 exactly. Generic sparse scatter and these named index identities need formal proof. This row identity exposes a nonzero c^2 coefficient for the chosen214minor: divide that factor, evaluate remaining213rows atc0, and use the explicit block inverse. It avoids dense numeral normalization.

Remaining after this core route: normalized actual two-circle parameter restriction must preserve nonzero polynomial (cannot assume arbitraryabc). On b0, parameter product uv1 givesa2 andc=-(u+u^-1); prove nonzero substitution via cleared univariate polynomial and its highest exponent, retaining poles and stopping semantics. Then actual challenge law and adversarial/oracle losses must be justified. R588 independent product-bound theorem is not that law.

Then query normalization leaves active rows because low chord support<91 and minactive114, but the additional H1 point/ordinary/structured moment residual image still requires an active-preserving kernel construction. The old13Gdirections allow active changes and cannot be substituted. Finally derive compatible target from actual legal C1 differences and retained terminal, not an arbitrary successful solve premise.

No determinant, universality, leak, privacy or100bit claim is made by this route. First formal target is the exact214active core minor nonzero on selected circle parameters, with a complete source-shaped index binding and no fixture-rank premise.
