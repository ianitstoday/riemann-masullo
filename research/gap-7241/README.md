# Evidence for the report on issue #7241

`spectralStripConvolution_traceCauchy_compact_block_series` (Theorem 10.3.2.1(1), pp. 453–455; ERRATA I314), taken
at strip width zero and any Sobolev exponent `s > 3`, implies a polynomial lower bound for the gaps between
distinct zeros of every row on the line `Re = a`, for every number field. The report is on the issue; these are
the Lean files it cites.

| File | What it is | Compiles at |
|---|---|---|
| `TraceCauchyRefereeStrip.lean` | The strip lemma only: 1325 lines, 22 `#print axioms` lines. Main theorem: `referee_strip_zero_width_gap_of_statement`. | `main` at `b4574b0` and at `578eb25` |
| `TraceCauchyReferee.lean` | The full file, 1948 lines: the above plus the same result for the line lemma `spectralLineConvolution_traceCauchy_scalar_shell`, which #7272 has since removed. | `b4574b0` only |
| `VerifierCheck.lean` | The independent checker's file: the full file plus its own restatements, whose hypothesis is the type of the library lemma and whose conclusion uses no scratch notation (`verifier_explicit_gap`, `verifier_explicit_line_gap`, `verifier_Ns_pos`). | `b4574b0` only |

## How to check

The files are not part of the library and nothing imports them. They start with `module` and use `import all`
on `Ch10_TraceSpectral/Sec3.lean` and `Sec2.lean` to reach private lemmas; that is acceptable in a scratch file
only. In a built checkout of `mccorvie/riemann-masullo`, copy a file anywhere inside the checkout and run

```
lake lean path/to/TraceCauchyRefereeStrip.lean
```

Exit status 0 in under a minute. Every theorem whose name does not end in `_library` or `_check` shows
`[propext, Classical.choice, Quot.sound]`. Those that do end so feed the library's lemma, which is still
`sorry`, into the implication, and show `sorryAx` as expected.

Three small steps coincide with mlyle's certificate on #6993 and are his: the choice of a good enumeration
(`referee_good_enumeration`, in the full file), the step `‖T‖ ≤ traceNorm T`, and a `norm_smul` helper.

Written by Claude Code agents; checked independently by a second agent.
