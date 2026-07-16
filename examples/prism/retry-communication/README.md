# PRISM bounded retry communication example

This self-contained PRISM 4.10.1 example models a communication operation as a
DTMC. Each attempt succeeds independently with probability `0.8`, and the
operation stops after at most three attempts.

## Assets and expected results

- [`retry-communication.pm`](retry-communication.pm): DTMC and `"cost"` reward
- [`retry-communication.props`](retry-communication.props): threshold,
  reachability, steady-state, and expected-cost properties
- [`expected-results.json`](expected-results.json): machine-readable expected
  values and comparison tolerance

| Property | Expected result |
|---|---:|
| `P>=0.99 [ F "success" ]` | `true` |
| `P=? [ F "failure" ]` | `0.008` |
| `S=? [ "success" ]` | `0.992` |
| `R{"cost"}=? [ F "done" ]` | `1.24` attempts |

Run the manifest contract rather than invoking an unpinned executable:

```bash
node scripts/run-example-manifest.js --id prism-retry-communication
```

The wrapper checks all four results and writes a machine-readable result file
under `.artifacts/manifest/prism-retry-communication/tool-output/`. The example
does **not** establish that `0.8` is a valid real-world success probability.
Replace it only with measured or otherwise justified data, and rerun a
parameter-sensitivity analysis before using the result for a decision.
