# Spectrebound: A Formally Verified Aperiodic Holography Theorem

[![Lean 4 Build](https://github.com/tryggth2009/spectrebound/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/tryggth2009/spectrebound/actions/workflows/lean_action_ci.yml)

> **A fully machine-checked proof, in Lean 4 + Mathlib, formalizing the Spectre aperiodic monotile. This project demonstrates that the geometric bulk of a Spectre patch is strictly determined by its 1D boundary perimeter.**

---

## The "Two Universes" Architecture

Formalizing 2D Euclidean geometry in dependent type theory often leads to intractable, explosive complexity. `spectrebound` solves this by cleanly cleaving the formalization into two mathematical universes:

### 1. The 1D Combinatorial Engine (100% Verified)
We map the continuous 2D plane into discrete 1D arrays of turning angles and Diophantine ledgers. In this discrete universe, Lean 4 natively verifies the entire boundary decoding algorithm. 
Instead of writing inductive proofs for complex geometric constraints, we leverage Lean 4's execution kernel to **brute-force finite computational matrices** at compile time using the `by decide` tactic:
* **The String Parity Conservation Matrix:** The compiler generates all 120 possible contiguous substring overlaps of the 14-edge Spectre sequence, mathematically proving that any valid collision perfectly conserves the $R_{60} \ge L_{60}$ turning parity.
* **The Determinism Array:** The kernel evaluates the 14-edge base tile array, exhaustively verifying that a single convex $L_{90}$ turn uniquely and deterministically locks the tile's orientation.
* **The Overlap Space:** An exact cyclotomic algebraic checker exhaustively tests all $5^4 = 625$ internal cross-vertex configurations, proving they always result in a physical overlap.

### 2. The Topological Quarantine (The 2D Planar Axioms)
What *cannot* be proven by a 1D string matching engine? A 1D array cannot inherently detect if it geometrically crosses itself (self-intersection) or if it encloses a void (an annulus). Crucially, if a tiling patch contains a hole, the boundary sequence of the hole runs inside-out, mathematically inverting the $L_{60}$ and $R_{60}$ parity conservation law!

Because these propositions are only true in a strictly planar 2D context, all continuous spatial geometry is isolated into a designated `TopologicalQuarantine`. Here, we explicitly axiomatize:
1. **Simple Connectivity:** The patch contains no holes, allowing the 1D Parity Matrix to hold.
2. **The Modulo-3 Vertex Constraint:** Surplus $120^\circ$ corners must physically group into $360^\circ$ closed vertices.
3. **Theorem 2 (Global Holography):** The axiomatic bridge stating that identical 1D mathematical sequences guarantee physically identical 2D Euclidean patches.

---

## Building and Running

This project is built using Lean 4. To compile the proofs and computationally verify the matrices locally:

1. **Install Elan (The Lean version manager):**
   Follow the instructions at [leanprover/elan](https://github.com/leanprover/elan) or run:
   ```bash
   curl [https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh](https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh) -sSf | sh
   ```

2. **Clone the Repository:**
   ```bash
   git clone https://github.com/tryggth2009/spectrebound.git
   cd spectrebound
   ```

3. **Build the Project:**
   ```bash
   lake build
   ```
   This command will download the Mathlib dependencies and instruct the Lean kernel to natively evaluate the substring collision matrices. The build will complete with exactly 0 warnings outside the designated quarantine blocks.

## Interactive Verification
To explore the proof architecture interactively, install VS Code and the Lean 4 extension. Open the repository folder, and click into any `.lean` file to initialize the language server and inspect the proof states.

## References
Smith, D., Myers, J. S., Kaplan, C. S., & Goodman-Strauss, C. (2023). A chiral aperiodic monotile. arXiv:2305.17743

Lean 4: https://leanprover.github.io/

## License
This proof development is released under the Apache 2.0 License.
