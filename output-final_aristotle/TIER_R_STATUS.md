# Tier R status

## Objective A

Implemented in `RequestProject/R_A1.lean` through `R_A6.lean`.

- R-A1: proved both directions of the Schur-complement PD criterion and the `IsPDq` extension theorem.
- R-A2: defined `GramState`, singleton construction, positive `margin`, and `margin_le`.
- R-A3: defined certificate-preserving `expand` and proved all block-faithfulness equations and `expand_pd`.
- R-A4: defined the explicit `(-A⁻¹b,1)` `haltWitness`, proved `halt_not_pd`, and proved the exact gate/PD equivalence.
- R-A5: defined all three spectral counts, proved their sum, proved the requested `IsPDq ↔ nMinus = 0 ∧ nZero = 0`, and proved congruence invariance of this PD readout. The stronger full three-count congruence theorem for indefinite matrices is not included; this is the partial-credit form explicitly allowed by R-A5.
- R-A6: reconstructed the audited `V5_5.M3` state literally by singleton, expand, expand; both Schur gates and exact matrix equality are proved. (`M3` is defined in namespace `V5_5`, while its entries use the required `V5_1.G`.)

## Objective B

- R-B1 is implemented: `checkPDq` is an executable exact-rational Boolean Sylvester checker (including symmetry), and `checkPDq_sound` proves its real cast is `IsPDq`.
- R-B2 and R-B3 were not attempted.

All listed Lean files build without `sorry`, `admit`, or `native_decide`.
