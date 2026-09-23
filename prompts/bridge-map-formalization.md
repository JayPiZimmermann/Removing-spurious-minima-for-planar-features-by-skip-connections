# Lane brief: formalize a scoped bridge result and expose usable corollaries

This is a worked example of how one formalization lane is dispatched. It shows
the level of detail a brief must carry: an explicit scope, an explicit freeze on
everything outside that scope, the mathematics settled on paper before any
encoding begins, the boundary cases that must not be absorbed, the formal and
paper-facing deliverables, and the closing duties. Reuse the shape and replace
the mathematics.

You are the runner and sole integrator for this lane. The research lead has
authorized this formalization explicitly, lifting the freeze on the formal tree
**for exactly this scope**: the bridge map `Π(o,a) = (oᵢ·‖aᵢ‖, aᵢ/‖aᵢ‖)ᵢ` from
raw trained weights `(o,a) ∈ ℝⁿ × (ℝ^d)ⁿ` to mass–direction coordinates, its
transfer of critical points and local minima on the domain where every row
`aᵢ ≠ 0`, and the resulting free-weight corollaries of the main theorems.
Nothing else in the formal tree may change.

## Environment rules (binding)

- **Never run a heavy Lean build on an interactive machine.** Submit it to the
  batch system through the campaign's build wrapper and read the durable log it
  writes. Never cancel a job this lane does not own.
- Load the relevant skills before touching anything: `skills/formalization-build`
  and `skills/formalization-conventions` for the formal work, and
  `skills/math-exposition` for the report.

## Mathematical content (settle by hand first; re-derive before encoding)

On `{(o,a) : ∀ i, aᵢ ≠ 0}`:

1. **Submersion.** Π is smooth there, and dΠ is surjective per unit: a sphere
   target `δw ⊥ w` is hit by `δa = ‖a‖·δw` (which adds nothing to the mass
   coordinate since `⟨w, δw⟩ = 0`), and the mass target by `δo = δc/‖a‖`.
2. **Critical-point transfer.** For `L` differentiable at `Π(o,a)` — both
   population losses in question are C¹ everywhere, since the relevant profile
   derivatives are continuous on `[−1,1]` — the point `(o,a)` is a critical
   point of `L∘Π` **iff** `Π(o,a)` is a critical point of `L`, criticality read
   as in the paper (mass gradients and projected sphere gradients zero).
   (⇐) is the chain rule; (⇒) is surjectivity of dΠ killing the covector.
3. **Local-minimum transfer.** Purely topological, no derivatives: Π is
   continuous, open, with continuous local sections (the identity section
   `(c,w) ↦ (o,a) = (c,w)`), so `(o,a)` is a local minimum of `L∘Π` iff
   `Π(o,a)` is a local minimum of `L`; strictness never transfers to the raw
   chart, because scaling orbits are loss-constant, so state ordinary minima
   only.
4. **Free-weight corollaries (the usable versions).** Compose with the existing
   main theorems: under the hypotheses of the centered benignity theorem and of
   its skip-connection corollary, every local minimum of the raw-weight loss
   with all rows nonzero and every induced mass `oᵢ‖aᵢ‖ ≥ 0` has loss zero.
   State both. The unit-mass slice (`oᵢ ≡ 1`) version follows and is what the
   experiments train; state it as its own corollary.

**Boundary discipline:** the domain restriction `aᵢ ≠ 0` is mathematically
necessary — at a zero row the raw loss is not differentiable, because the unit's
contribution is a degree-one homogeneous even function of `aᵢ`. Do NOT attempt
to absorb the zero-row case into these statements. **Stretch goal, separate
declarations, only if time permits:** formalize the one-sided zero-row
comparison — minimality against `aᵢ = tu, t > 0` gives a sign condition on the
residual force at `u`, criticality of the nonzero rows makes it vanish at each
live direction, and the residual–loss pairing then forces zero loss. Closing it
would let the paper drop its remaining coverage exception for that remark.

## Formal side

- One new leaf module carrying the definitions (the bridge map and its domain)
  and statements 1–3, plus a public-facing module carrying the usable
  corollaries 4 in the paper's own vocabulary. Follow the naming skill; keep
  hypotheses literal (nonnegative induced masses, all rows nonzero).
- Prefer elementary encodings over manifold machinery: criticality via the
  explicit gradient formulas the tree already uses, componentwise, and the
  sphere gradient as the projected Euclidean gradient. The library supplies norm
  smoothness away from zero and all the calculus needed.
- Add the new public declarations to the public import surface and to the
  verifier's statement manifest with exact post-build types; build every touched
  module through the batch system and rerun the verifier there.

## Paper side (only after the formal side builds green)

- Add a small numbered theorem in the appendix section that already discusses
  the normalization and the topology bridge, stating 2–4 in the paper's
  notation, with a structured proof environment carrying the short written
  argument: the chain-rule half expanded from the existing remark, the
  local-minimum half via openness and continuous sections. Put definitions
  before the statement, one term per object, and attach the formal-counterpart
  identifier using the next free id from the generator that maintains the
  paper-to-Lean table; add its row and dependency entries and regenerate.
- The remark in the setting section now cites the new theorem instead of proving
  its transfer inline, and keeps its one-sided zero-row comparison. The
  introduction's coverage exception stays unless the stretch goal lands, in
  which case update both.
- Write the annotation file for the new theorem in the standard format, add its
  claim-ledger row, and refresh the pinned paper-to-Lean links after the final
  push.
- Rebuild the paper only where the TeX toolchain exists; zero undefined
  references are required.

## Closing duties

Commit narrowly, in separate commits for the formal modules, the paper files,
and the annotations plus regenerated tables. Rebase onto the current upstream
state, refresh the pinned links, and push. The final report gives each new declaration
with its exact type, the build evidence from the batch system, the paper diffs,
and whether the stretch goal landed.
