# Evidence for the report on issue #7220

`spectralStripJet_order_and_margin_locally_finite_multiple_zeros` (Proposition 10.2.2.2, pp. 446–447; ERRATA I277)
implies a height-independent bound for the multiplicities of the zeros of the Riemann zeta function, and over ℚ is
equivalent to a statement about Dirichlet L-functions that lies between two open statements. The report is on the
issue; these are the Lean files it cites.

| File | What it is |
|---|---|
| `Gap7220.lean` | The full scratch file: 1205 lines, 35 `#print axioms` lines at the end. |
| `Gap7220Min.lean` | An excerpt, 163 lines: the implication for the Riemann zeta function alone, with the hypothesis written out. |
| `Gap7220.axioms.txt` | The axioms of each of the 35 theorems, as printed. |

## How to check

The files are not part of the library and nothing imports them. They use `import all` to reach private lemmas of
`Ch10_TraceSpectral/Sec2.lean`, `Ch03_IdelicZeta/Sec2.lean` and
`ForMathlib/NumberTheory/NumberField/DedekindZeta/MultipleZero.lean`; that is acceptable in a scratch file only.

In a built checkout of `mccorvie/riemann-masullo`, copy a file anywhere inside the checkout and run

```
lake lean path/to/Gap7220.lean
```

Checked at commits `5b158be` and `578eb25` of `main`: exit status 0 in under half a minute. Of the 35 theorems,
28 show `[propext, Classical.choice, Quot.sound]`. The other 7 (`locallyFiniteAt_of_target` and the six
`…_from_…` theorems) show `sorryAx`: they apply the implications to the library's lemma as it stands, which is
still `sorry`.

Written by Claude Code agents; checked independently by a second agent.
