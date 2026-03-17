# Appendix B: Tool Installation Guide

Tool execution in this book is provided through the following two tracks, with **reproducibility (minimizing environment differences)** treated as the priority.

1. **Container (recommended)**: prepare a unified environment with a devcontainer  
2. **Local**: run with minimum dependencies such as Java, `curl`, and `unzip`

The commands below are representative examples. Distribution formats and prerequisites may change, so consult Appendix E on primary sources when necessary.

By following this appendix, you should be able to reproduce at least **one model checking workflow** (`Alloy`/`TLC`/`Apalache`) and **one program verification workflow** (`Dafny`).

## Target Tools (Minimum Set)

- Alloy `6.x` (CLI execution)
- TLA+ `TLC` (`tla2tools.jar`)
- Apalache (SMT-based verification for TLA+)
- Dafny (verifier)

Notes:
- Theorem provers such as `Rocq` and `Isabelle` have larger dependency footprints, so this appendix primarily points to primary sources for them in Appendix E.
- `Lean 4` is included here only as a **minimal setup** at the end of the appendix as an optional path through the book.

## Recommended: devcontainer (Container Workflow)

Prerequisites:
- Docker is available
- You have an editor that can work with a devcontainer, such as `VS Code` with `Dev Containers`

Steps:
1. Open this repository in the devcontainer by using `.devcontainer/`
2. On the first startup, `tools/bootstrap.sh` runs and places tools under `tools/.cache/`
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

## Local Workflow (Non-container)

### Prerequisites (Linux/WSL)

- Java 17 or later, required to run `TLC`, `Alloy`, and `Apalache`
- `curl` and `unzip`

The procedure is the same as in the devcontainer: run `bash tools/bootstrap.sh` to fetch the required files and then execute the scripts under `tools/*.sh`.

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

## CI (Automated Execution)

In `GitHub Actions`, `.github/workflows/formal-checks.yml` provides pull-request jobs for lightweight checks and nightly jobs for deeper exploration.  
If you want to run the equivalent lightweight path locally, execute `bash examples/ci/pr-quick-check.sh`.
