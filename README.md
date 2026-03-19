# Countermath Translations

Formalizing mathematical statements from the [COUNTERMATH](https://github.com/THUKElab/COUNTERMATH/tree/main) dataset into Lean 4.

## Project Structure

* **Countermath.lean**: Contains decidable propositions. These are verified using **LSpec** and **SlimCheck**. These tests run on discrete types (like `Nat`, `Int`, `Bool`, and `Fin n`, etc).
* **Uncheckable.lean**: Contains non-decidable or infinite-dimensional statements (e.g., proofs from topology, real analysis, ...). These are stored as `theorem` declarations with `sorry` and require manual tactic-based proofs. For purposes of this project, proofs are either given using tactics or otherwise left with `sorry`.



## Setup

1.  **Initialize Project**:
    ```bash
    lake init countermath math
    ```

2.  **Fetch Mathlib Binaries**:
    ```bash
    lake exe cache get
    ```

3.  **Update Dependencies**:
    ```bash
    lake update
    ```

4.  **Verify Installation**:
    Open a Lean file and ensure `import Mathlib` does not show errors. If it does, restart the Lean server in your editor with `CMD + Shift + V` for MacOS or `CTRL + Shift + V` for Windows/Linux.

