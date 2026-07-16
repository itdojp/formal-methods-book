---
layout: book
title: "Appendix B: Tool Setup and Verification Quick Start"
description: "The shortest reproducible path to running the companion examples for Alloy, TLC, Apalache, Dafny, and Lean 4."
locale: "en"
lang: "en"
source_path: "src/en/appendices/appendix-b.md"
translation_status: "partial"
translation_source_commit: "a4be778350d24c089d00bdce6d31fd736cc6cf1e"
translation_reviewed_at: "2026-07-16"
translation_tracking_issue: "https://github.com/itdojp/formal-methods-book/issues/328"
---
# Appendix B: Tool Setup and Verification Quick Start

> **Translation status: Partial.** Reviewed against Japanese source commit [`a4be778350d2`](https://github.com/itdojp/formal-methods-book/commit/a4be778350d24c089d00bdce6d31fd736cc6cf1e) on 2026-07-16.
> Some content, headings, examples, tables, or references remain partially synchronized. [Track the remaining work](https://github.com/itdojp/formal-methods-book/issues/328).

This appendix gives the shortest reproducible path to running the book's companion examples. It prioritizes **reproducibility (minimizing environment differences)** over local customization.

1. **Container (recommended)**: use a devcontainer for a unified environment  
2. **Local**: run the same scripts with minimum dependencies such as Java, `curl`, and `unzip`

The commands below are representative examples. Distribution formats and prerequisites may change, so consult Appendix E on primary sources when necessary.

You do not need every tool before you begin reading. By following this appendix, you should be able to reproduce at least **one model checking workflow** (`Alloy`/`TLC`/`Apalache`) and **one program verification workflow** (`Dafny`).

## Target Tools (Minimum Set)

- Alloy `6.x` (CLI execution)
- TLA+ `TLC` (`tla2tools.jar`)
- Apalache (SMT-based verification for TLA+)
- Dafny (verifier)

Notes:
- Theorem provers such as `Rocq` and `Isabelle` have larger dependency footprints, so this appendix primarily points to primary sources for them in Appendix E.
- `Lean 4` is included here only as a **minimal setup** at the end of the appendix as an optional path through the book.
- SPIN, NuSMV, CBMC, Quint, PRISM, Tamarin, and SymbiYosys belong to the `nightly` lane, and this appendix also documents one `cvc5` + `Carcara` proof-certificate recheck path there. Additional prerequisites for source builds and archive-layout validation are listed below.

## Tool Lane Inventory and Execution Guarantee {#tool-lane-inventory}

`tools/tool-manifest.json` is the source of truth for every tool's classification, executable version, distribution digest, artifact limits, and update procedure.
`pr-quick` runs small examples related to a PR diff, `nightly` uses an independent per-tool matrix, and `optional/manual` runs only through an explicit `workflow_dispatch` selection.
`documentation-only` means that the book introduces the tool or service but this repository does not guarantee its version, environment, or result.
Indirect use of an embedded solver does not constitute a standalone execution guarantee for that solver.

<!-- tool-inventory:start -->
| Tool / service | lane | Verified version | Rationale |
| --- | --- | --- | --- |
| Alloy Analyzer | pr-quick | 6.2.0 | Four small-scope examples are reproducible within the PR budget. |
| TLC | pr-quick | 1.7.4 | Checks a finite model with pinned cfg, worker count, seed, and timeout. |
| Apalache | pr-quick | 0.52.1 | A short bounded invariant check is reproducible on every PR. |
| Dafny | pr-quick | 4.11.0 | The minimal verification example is fast and stable. |
| SPIN | nightly | 6.5.2 | Source build and state exploration run in an isolated nightly tool job. |
| NuSMV | nightly | 2.7.1 | The official source build has extra dependencies and is isolated to nightly. |
| CBMC | nightly | 6.10.0 | Runs the pinned Ubuntu package and bounded check in an isolated nightly job. |
| Quint | nightly | 0.32.0 | Uses the official single binary for typecheck/test with a fixed seed and TypeScript backend. |
| PRISM Model Checker | nightly | 4.10.1 | Downloads the pinned roughly 41 MB official distribution and reproduces quantitative properties in an isolated nightly job. |
| Tamarin Prover | nightly | 1.12.0 | Downloads pinned official Tamarin and supported Maude distributions and reproduces attack traces and lemmas in an isolated nightly job. |
| SymbiYosys (sby) | nightly | v0.67-4-gfea6e46 | Downloads an approximately 733 MB pinned OSS CAD Suite and reproduces RTL BMC, k-induction, and cover tasks in an isolated nightly tool job. |
| Kani Rust Verifier | optional/manual | 0.67.0 | Requires a pinned Rust nightly, so it is limited to explicit manual dispatch. |
| TLA+ Toolbox | documentation-only | — | GUI/editor environment; outside this repository's CLI guarantee. |
| TLA+ VS Code extension | documentation-only | — | Editor support is separate from CLI checks and its extension version is not pinned. |
| Community Z Tools (CZT) | documentation-only | — | Reference-only Z tooling with no executable asset. |
| FDR | documentation-only | — | CSPM examples are shown, but distribution/licensing and CI are not pinned. |
| ProB | documentation-only | — | Mentioned only; no executable asset or pinned environment. |
| PAT | documentation-only | — | Mentioned only; no executable asset or pinned environment. |
| nuXmv | documentation-only | — | Introduced as distinct from NuSMV; CI guarantees NuSMV only. |
| Java PathFinder | documentation-only | — | Mentioned as an option/exercise; no executable asset. |
| UPPAAL | documentation-only | — | Not automated due to GUI, licensing, and distribution constraints. |
| TIMES | documentation-only | — | Reference-only real-time verification tool. |
| Rocq / Coq | documentation-only | — | No pinned proof project, opam switch, or library set. |
| Lean 4 / Lake / mathlib / elan | documentation-only | — | No proof project or dependency revision; the Linux distribution is also large. |
| Isabelle/HOL | documentation-only | — | Reference-only; no pinned session/build environment. |
| Agda | documentation-only | — | Reference-only; no pinned project or libraries. |
| HOL4 | documentation-only | — | Mentioned as an Aeneas target; no execution contract. |
| F* | documentation-only | — | Mentioned as a target/related technology; no execution contract. |
| Frama-C | documentation-only | — | Reference-only; plugin and solver configuration are not pinned. |
| VeriFast | documentation-only | — | Reference-only; no executable asset. |
| SPARK | documentation-only | — | Industrial toolchain/licensing environment is not pinned. |
| Why3 | documentation-only | — | Execution configuration including backend solvers is not pinned. |
| Verus | documentation-only | — | Rust/Z3/revision execution stack is not pinned. |
| Creusot | documentation-only | — | Why3/solver/Rust combination is not pinned. |
| Prusti / Viper | documentation-only | — | Rust/Viper toolchain and executable asset are not pinned. |
| Aeneas / Charon | documentation-only | — | No pinned end-to-end contract including a proof target. |
| Z3 | documentation-only | — | Indirect use by other tools is not counted as a standalone solver guarantee. |
| cvc5 / CVC4 | nightly | 1.3.4 | Verifies and re-extracts a pinned official solver asset, rebuilds an independent Alethe checker from source nightly, and rechecks an UNSAT certificate. |
| Yices | documentation-only | — | Reference-only; no pinned executable asset. |
| MathSAT | documentation-only | — | Reference-only; licensing/distribution environment is not pinned. |
| SCADE | documentation-only | — | Commercial/GUI toolchain; not a mandatory CI dependency. |
| Simulink | documentation-only | — | Industry-case reference only; no licensed environment is pinned. |
| SAW | documentation-only | — | Industry-case reference; no s2n verification asset is included. |
| Cedar Analysis | documentation-only | — | Service/API and tools evolve; no policy asset is pinned. |
| Bedrock Guardrails Automated Reasoning checks | documentation-only | — | External service/region/API constraints are not mandatory CI dependencies. |
| Solidity SMTChecker | documentation-only | — | Solidity/compiler/solver stack and contract asset are not pinned. |
| Aptos Move Prover | documentation-only | — | Move toolchain and contract asset are not pinned. |
| Certora Prover | documentation-only | — | External/industrial toolchain is not a mandatory CI dependency. |
| LeanDojo | documentation-only | — | Reference-only AI proof-assistance evaluation framework. |
| Lean Copilot | documentation-only | — | Reference-only AI proof assistance; model/project not pinned. |
| AlphaProof / AlphaGeometry 2 | documentation-only | — | Research-result reference with no redistributable CLI contract. |
| DeepSeek-Prover-V2 | documentation-only | — | Research-result reference; model/runtime not pinned. |
| ProofGym | documentation-only | — | Evaluation-framework reference; dataset/runtime not pinned. |
| APOLLO | documentation-only | — | Research-result reference; no execution contract. |
<!-- tool-inventory:end -->

The cvc5 `nightly` classification in the inventory above denotes the narrow
`cvc5-alethe-unsat-certificate` **pinned nightly contract**: one
`cvc5 1.3.4` to `Alethe` to `Carcara 1.1.0` recheck path, not a blanket
guarantee for cvc5 as a whole.

Every executable entry states its timeout, memory budget, seed, scope, depth, and bound.
Artifacts record the tool version, command, per-file SHA-256 and aggregate input hash, exit code, stdout/stderr, and distinct `success`, `counterexample`, `unknown`, timeout, and resource-exhaustion outcomes.
Retention is 14 days; stdout/stderr is limited to 16 MiB per entry and tool output to 64 MiB per entry.
The runner enforces timeout and stdout/stderr limits and checks retained tool output after execution. `memoryMiB`, however, is a declared CI-capacity budget, not an OS/cgroup-enforced limit. Consequently, `resource-exhausted` covers detectable output excess; an OOM kill may surface as `tool-error` or a runner failure.

- `quint-counter`: typechecks and tests [examples/quint/counter.qnt](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/quint/counter.qnt) with Quint 0.32.0, the bundled TypeScript evaluator, seed `20260716`, and one sample per test. It does not implicitly download the separately distributed Rust evaluator.
<!-- example-contract: quint-counter -->
【Tool-compliant (runs as-is)】
```bash
node scripts/run-example-manifest.js --id quint-counter
```

- `kani-abs`: verifies the `abs_is_nonnegative` harness in [examples/kani/abs.rs](https://github.com/itdojp/formal-methods-book/blob/{{site.github.build_revision|default:'main'}}/examples/kani/abs.rs) with Kani 0.67.0, a pinned Rust nightly, and unwind bound 1. Because it requires an additional download and execution budget, it is `optional/manual` and never starts from a PR or schedule.

After cache restore, the bootstrap rechecks the SHA-256 of both the Quint binary and the PRISM archive.
PRISM 4.10.1 is re-extracted from its official GPL-2.0 Linux x86-64 archive on every run so that its absolute launcher path is rebuilt; the repository, CI artifacts, and Pages do not redistribute the tool binary.
Tamarin Prover 1.12.0 (GPL-3.0) and its supported Maude 3.5.1 (GPL-2.0-or-later) are also re-extracted from official SHA-256-pinned archives. Tamarin artifacts retain lemma results and the flawed model's attack graph, but not either binary. Because an attack graph preserves model constants, a model must not contain real secrets.
SymbiYosys is re-extracted on every run from the SHA-256-pinned official OSS CAD Suite 20260716 Linux x64 archive. Bootstrap checks archive paths, duplicate entries, resolved symlink targets, special files, the suite version, and the SBY, Yosys, and Bitwuzla versions and source commits recorded in bundled metadata and license files. The suite release-tag commit is recorded separately as source provenance rather than treated as an identity embedded in the distribution. SBY and Yosys use the ISC license and Bitwuzla uses MIT; other bundled components retain their own licenses. Artifacts keep normalized results and only the required VCD traces, not the suite archive, extracted binaries, or solver models.
Only input hashes, standard output, and expected-value comparisons are retained.
Kani is re-extracted from its verified archive on every run, and the dated Rust channel manifest is also verified by SHA-256. rustup then verifies the Rust components against the checksums recorded in that manifest.
<!-- example-contract: kani-abs -->
【Tool-compliant (runs as-is)】
```bash
node scripts/run-example-manifest.js --id kani-abs
```

Version updates are checked monthly against the official release/tag and asset digest, then reviewed in a dedicated version-only PR with a clean-cache run and output-contract comparison.
Arbitrary release assets are not package references managed by Dependabot or Renovate and must not be treated as automatically updated.

## Recommended: devcontainer (Fastest Reproducible Path)

Prerequisites:
- Docker is available
- You have an editor that can work with a devcontainer, such as `VS Code` with `Dev Containers`

Steps:
1. Open the book's companion repository in a devcontainer by using `.devcontainer/`
2. On the first startup, `tools/bootstrap.sh` fetches the tool distributions and places them under `tools/.cache/`
3. Run the following commands to execute the sample workflows

```bash
# Fetch tools (safe to rerun)
bash tools/bootstrap.sh

# Alloy (confirm SAT)
bash tools/alloy-check.sh --verbose examples/alloy/collection.als

# TLC (confirm No error)
bash tools/tlc-run.sh --config examples/tla/QueueBounded.cfg examples/tla/QueueBounded.tla

# Apalache (confirm NoError)
bash tools/apalache-check.sh --config examples/apalache/Counter.cfg --length 10 --init Init --next Next --inv Inv examples/apalache/Counter.tla

# Dafny (confirm 0 errors)
bash tools/dafny-verify.sh examples/dafny/Abs.dfy
```

Expected output (excerpt):
- Alloy: `SAT` (for example, a line containing `SAT` appears)
- TLC: `Model checking completed. No error has been found.`
- Apalache: `The outcome is: NoError` and `EXITCODE: OK`
- Dafny: `finished with ... verified, 0 errors`

Outputs such as counterexamples and logs are stored under `.artifacts/`. They are also uploaded as CI artifacts.
If any command fails, check the Java version, shell environment, and the primary sources listed in Appendix E before modifying the helper scripts.

## Local Workflow (Without a Container)

### Prerequisites (Linux/WSL)

- Java 17 or later, required to run `TLC`, `Alloy`, and `Apalache`
- `curl` and `unzip`

Use the same flow as in the devcontainer: run `bash tools/bootstrap.sh` to fetch the required files, then execute the scripts under `tools/*.sh`.

### Additional prerequisites for the nightly lane (Ubuntu 24.04 x86-64)

`node scripts/run-example-manifest.js --lane nightly` executes 12 entries across SPIN 6.5.2, NuSMV 2.7.1, CBMC 6.10.0, Quint 0.32.0, PRISM 4.10.1, Tamarin Prover 1.12.0, and SymbiYosys. SPIN and NuSMV need the source-build prerequisites below, and SymbiYosys uses Python 3 to validate its archive layout. CBMC uses a pinned Ubuntu 24.04 x86-64 deb, Quint uses a pinned single binary, PRISM uses a pinned official archive of roughly 41 MB, Tamarin uses two pinned official archives with supported Maude 3.5.1, and SymbiYosys uses an approximately 733 MB OSS CAD Suite 20260716 Linux x64 archive, so this procedure targets that environment or a compatible one.

```bash
sudo apt-get update
sudo apt-get install --yes \
  bison build-essential flex g++ gcc m4 patch pkg-config \
  python3 python3-venv xz-utils

python3 -m venv tools/.tmp/nusmv-build-tools
tools/.tmp/nusmv-build-tools/bin/pip install \
  --disable-pip-version-check \
  --require-hashes \
  --requirement tools/nusmv-build-requirements.txt

PATH="$PWD/tools/.tmp/nusmv-build-tools/bin:$PATH" \
  node scripts/run-example-manifest.js --lane nightly
```

The downloaded tools are pinned by commit/version and SHA-256, and the Meson/Ninja packages are pinned by hashes in the requirements file. On native macOS, native Windows, or a different CPU architecture, use an Ubuntu 24.04 x86-64 container, WSL2, or the GitHub Actions `workflow_dispatch` instead of treating this lane as locally portable.

### Additional prerequisites for independent proof-certificate rechecking (`cvc5` + `Carcara`)

The `cvc5-alethe-unsat-certificate` contract is intended to download the
official `cvc5 1.3.4` release asset, generate an Alethe proof, download the
pinned `Carcara 1.1.0` compatibility source archive, and build the checker from
source.
Ubuntu 24.04 x86-64, or a compatible Linux environment, is the recommended
target.

```bash
sudo apt-get update
sudo apt-get install --yes build-essential m4

# Confirm that rustup and cargo are on PATH. The bootstrap installs and uses
# the pinned Rust/Cargo 1.87.0 toolchain.
rustup --version
cargo --version

node scripts/run-example-manifest.js --id cvc5-alethe-unsat-certificate
```

This lane does not redistribute the downloaded `cvc5` binary or the built
`Carcara` executable through the repository or Pages.
The official Rust channel-manifest digest acts as a provenance sentinel. After
rustup checks the fixed-version component checksums, the bootstrap also matches
the installed rustc/Cargo commits and host against manifest values. It does not
claim that the independently downloaded manifest file is passed into rustup.
The certificate is capped at 1 MiB and checker output at 64 KiB.
Retained evidence is limited to the SMT-LIB input, the manifest expected-result contract, the
generated proof certificate, stdout/stderr, input hashes, and version metadata.
Even when the checker passes, the result only validates the encoded problem as
checked; it does not validate the natural-language requirement, the original
specification, the encoder, or unmodeled assumptions.

To rerun only PRISM, use:

```bash
node scripts/run-example-manifest.js --id prism-retry-communication
```

This reproduces the numerical contract for one DTMC and four properties; it does not establish that the teaching success probability of 0.8 is valid for a real system.

To rerun only the flawed and fixed Tamarin models, use:

```bash
node scripts/run-example-manifest.js --id tamarin-replay-flawed
node scripts/run-example-manifest.js --id tamarin-replay-fixed
```

The flawed model's `counterexample` is an expected passing result. The fixed model checks that all four stated lemmas are `verified` under the same symbolic-model configuration.

To rerun only the flawed BMC, fixed proof, and fixed cover contracts for SymbiYosys, use:

```bash
node scripts/run-example-manifest.js --id sby-rtl-arbiter-flawed-bmc
node scripts/run-example-manifest.js --id sby-rtl-arbiter-fixed-prove
node scripts/run-example-manifest.js --id sby-rtl-arbiter-fixed-cover
```

The flawed design's `counterexample` is an expected passing result. The proof `PASS` is a k-induction result relative to the stated property and assumptions, while the cover `PASS` means that the requested witness state was reached.

### OS-specific Notes (Key Points)

- Windows:
  - **Running under `WSL2` is recommended** so that the assumptions behind the tool distributions and shell scripts match the environment
  - Install Java inside the WSL environment rather than relying on Java installed on the Windows side
- macOS:
  - Because `timeout` is not available by default, using `tools/tlc-run.sh --time-limit` requires a provider such as `gtimeout` (for example via `coreutils` from `Homebrew`). `tools/tlc-run.sh` automatically detects `timeout` or `gtimeout`.
  - The Dafny distribution fetched by `tools/bootstrap.sh` targets Linux, so on macOS use the official macOS distribution or install Dafny via `dotnet tool`
- Linux:
  - Package names for Java differ by distribution. For example, `Ubuntu` and `Debian` use `openjdk-17-jre`.

## Lean 4 Setup (Minimal Setup / Optional)

In this book, `Lean 4` is positioned as an option for making theorem proving a maintainable engineering asset. See Chapter 9 for the conceptual role. Here, only the shortest path to a minimal setup is shown; consult the primary sources for detail.

### What to Know First (Minimum)

- **`elan`**: a tool for managing the Lean toolchain, including the Lean compiler and related components
- **`Lake`**: Lean 4’s build and dependency-management tool, used for creating and building projects
- **VS Code extension**: provides the interactive development experience, including type-checking results and goal display

### Steps (Representative Example)

1. Install `elan` by following the primary source
2. Install `VS Code` and the `Lean 4` extension by following the primary source
3. Create a minimal `Lean 4` project and confirm that it starts correctly

```bash
mkdir -p lean-sandbox && cd lean-sandbox
lake init hello
lake build
```

Confirm:
- Open `lean-sandbox/` in `VS Code` and open the generated `.lean` file
- Confirm that no error appears and that the toolchain is active

Primary Sources (Official / Representative):
- Lean official site: <https://lean-lang.org/>
- Lean 4 (`GitHub`): <https://github.com/leanprover/lean4>
- `elan`: <https://github.com/leanprover/elan>
- `VS Code` Lean 4 extension: <https://github.com/leanprover/vscode-lean4>

## Companion Automation (Reference Only)

The companion repository includes `GitHub Actions` workflows in `.github/workflows/formal-checks.yml` for lightweight pull-request checks and deeper nightly exploration.  
If you want to run the equivalent lightweight path locally, execute `bash examples/ci/pr-quick-check.sh`.
