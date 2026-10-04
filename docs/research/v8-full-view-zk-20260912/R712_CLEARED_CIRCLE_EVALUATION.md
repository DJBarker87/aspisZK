# R712: Cleared circle evaluation

Canonical Lean target: `AspisV8R19/R712ClearedCircleEvaluation.lean`, SHA-256 `18d8e29006b385f4dd45131dee744f34a6a6d63feb3e366267b83e9a1a945a4b`. The target was compiled at source revision `a5e3046384337bf9a833a613cc72ae440d23741a` using Lean 4.32, `-j1 -M4500`, and a systemd scope with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

The final focused run was `1791129102855843000`: exit 0, wall time 1.62 s, peak Lean-child RSS 3,269,368 KiB, and swap 0. Its four complete `#print axioms` reports contain only `[propext, Classical.choice, Quot.sound]`.

For every field, R712 proves that for nonzero `u`, the R708 cleared polynomial evaluates as

```lean
(cleared P).eval u = u ^ P.natDegree * P.eval (-(u + u⁻¹))
```

and its degree is at most `2 * P.natDegree`. For a finite field, a nonzero `P`, and `2 * P.natDegree + 1 < Fintype.card F`, it proves that some nonzero `u` has `P.eval (-(u + u⁻¹)) ≠ 0`. The proof uses the nonzero cleared polynomial and the finite-field polynomial evaluation bound; it does not reduce a concrete degree or field element.

The package preserves every focused R712 target record: early evaluation drafts and API failures (`1791128975225023000`, `1791128999275123000`, `1791129012451368000`, `1791129026089573000`), green evaluation helper (`1791129033552486000`), green degree helper (`1791129055264914000`), the first finite-field composition failure (`1791129080111810000`), its green composition (`1791129089247134000`), and the final axioms-complete run (`1791129102855843000`).

R712 is generic field algebra. It does not prove the evaluation identity for an actual circle parameter, an actual native circle law, any R707 application, nonzeroness of the multivariate determinant polynomial, a sampling distribution or loss, or privacy or security.
