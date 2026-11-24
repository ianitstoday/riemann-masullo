# Evidence for the note on issue #7336

`LaurentNecessity.lean` (277 lines): if any enumeration of the polar coefficients of the primary quotient has a
biorthogonal Schauder basis, then along every pole lattice, over the centers of multiplicity at least two, the
ratio of the second Laurent coefficient of the correcting factor to the leading one, times the leading Fourier
jet of any theta class, tends to zero (`sLocalPolarOrbital_basis_ratio_tendsto_of_frechet`). This is the
machine-checked step of the argument that a polar basis forces a polynomial bound on that ratio; the rest of the
argument is by hand and is in the note on the issue.

`Sec3a-desaturate.patch`: a proposal, not applied anywhere. The hypothesis `IsSaturatedPlaceSet` is not used by
any proof in `Ch07_SchauderBasesZeta/Sec3a.lean`; the patch deletes it from the 27 statements that carry it.
Checked at `b4574b0` only (three of its 45 hunks no longer apply on later `main`). Changing statements is the
integrator's decision.

## How to check

The Lean file is not part of the library. It starts with `module` and uses `import all` on
`Ch07_SchauderBasesZeta/Sec3a.lean` (scratch only). In a built checkout of `mccorvie/riemann-masullo` at commit
`b4574b0`, copy it anywhere inside the checkout and run `lake lean path/to/LaurentNecessity.lean`: exit status 0
in about half a minute; the three main theorems show `[propext, Classical.choice, Quot.sound]`.

Written by Claude Code agents; checked independently by a second agent.
