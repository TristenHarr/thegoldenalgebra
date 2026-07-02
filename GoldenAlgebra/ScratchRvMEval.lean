import rh

/-!
# ScratchRvMEval — discharging `RvMRectangleMainTermEvaluation`

The structure `OverflowResidueRH.BacklundTuring.RvMRectangleMainTermEvaluation`
(rh.lean ~15007) asks for a function `Sarg : ℝ → ℝ` together with the identity

  `zetaWeightedZeroCountInHeightSlab D.R.bottom D.R.top ... = riemannVonMangoldtMainTerm T + Sarg T`

where `D : RvMRectangleData T` has `D.R.top = T` (`top_eq`).

Key observation: this is a *pure algebraic identity*, no residual analytic input.

* The slab count `(A,B]` equals the cumulative difference `N(B) − N(A)`
  (`zetaWeightedZeroCountInHeightSlab_eq_sub`), with `A = D.R.bottom`, `B = D.R.top = T`.
* The cumulative count `N(T)` decomposes as
  `N(T) = riemannVonMangoldtMainTerm T + concreteS T`
  (`concreteS_eq_zeta_count_sub_riemannVonMangoldtMainTerm`, an unfolding of the
  *definition* of `concreteS` — `riemannVonMangoldtMainTerm = smoothMainTerm`).

Hence with
  `Sarg T' := concreteS T' − (N(bottom) : ℝ)`
the identity holds, and `concreteS` is exactly the Riemann–von Mangoldt argument
fluctuation `S(T) = N(T) − N₀(T)`.  The `(N(bottom))` correction accounts for the
fact that the *slab* count `(bottom, T]` omits the (finite, height‑< bottom) zeros
that the cumulative `N(T)` includes; for the standard usage `D.R.bottom` is a fixed
positive base height so this is a fixed real constant.
-/

namespace OverflowResidueRH
namespace BacklundTuring
namespace ZetaRectangle

/-- **Main result (this scratch file).**  Discharge the per‑height main‑term
evaluation obligation `RvMRectangleMainTermEvaluation` for an arbitrary RvM
rectangle `D : RvMRectangleData T`, with **no** residual hypothesis.

The argument term is `Sarg T' = concreteS T' − N(bottom)`; the cast of the
cumulative zero count `N(D.R.bottom)` at the fixed bottom height is the slab
base correction.  The `evaluation` field is a pure algebraic identity. -/
noncomputable def rvMRectangleMainTermEvaluation
    {T : ℝ} (D : RvMRectangleData T) :
    RvMRectangleMainTermEvaluation D where
  Sarg := fun T' =>
    concreteS T'
      - (zetaWeightedZeroCountUpToHeight D.R.bottom D.bottom_nonneg : ℝ)
  evaluation := by
    -- Abbreviations for the two endpoint heights.
    -- bottom := D.R.bottom (nonneg), top := D.R.top = T.
    have htop : D.R.top = T := D.top_eq
    -- The slab count is the cumulative difference N(top) − N(bottom).
    have hslab :
        (zetaWeightedZeroCountInHeightSlab
            D.R.bottom D.R.top D.bottom_nonneg D.R.hbottom_lt_top.le : ℕ) =
          zetaWeightedZeroCountUpToHeight D.R.top
              (le_trans D.bottom_nonneg D.R.hbottom_lt_top.le)
            - zetaWeightedZeroCountUpToHeight D.R.bottom D.bottom_nonneg :=
      zetaWeightedZeroCountInHeightSlab_eq_sub
        D.bottom_nonneg D.R.hbottom_lt_top.le
    -- Monotonicity gives N(bottom) ≤ N(top), so the ℕ subtraction is genuine.
    have hmono :
        zetaWeightedZeroCountUpToHeight D.R.bottom D.bottom_nonneg ≤
          zetaWeightedZeroCountUpToHeight D.R.top
            (le_trans D.bottom_nonneg D.R.hbottom_lt_top.le) :=
      zetaWeightedZeroCountUpToHeight_mono
        D.bottom_nonneg
        (le_trans D.bottom_nonneg D.R.hbottom_lt_top.le)
        D.R.hbottom_lt_top.le
    -- Cast the ℕ slab identity to ℝ, handling the truncated subtraction.
    have hslabR :
        (zetaWeightedZeroCountInHeightSlab
            D.R.bottom D.R.top D.bottom_nonneg D.R.hbottom_lt_top.le : ℝ) =
          (zetaWeightedZeroCountUpToHeight D.R.top
              (le_trans D.bottom_nonneg D.R.hbottom_lt_top.le) : ℝ)
            - (zetaWeightedZeroCountUpToHeight D.R.bottom D.bottom_nonneg : ℝ) := by
      rw [hslab]
      rw [Nat.cast_sub hmono]
    -- N(top) = riemannVonMangoldtMainTerm top + concreteS top.
    have hN :
        (zetaWeightedZeroCountUpToHeight D.R.top
            (le_trans D.bottom_nonneg D.R.hbottom_lt_top.le) : ℝ) =
          riemannVonMangoldtMainTerm D.R.top + concreteS D.R.top := by
      have h :=
        concreteS_eq_zeta_count_sub_riemannVonMangoldtMainTerm
          (T := D.R.top)
          (le_trans D.bottom_nonneg D.R.hbottom_lt_top.le)
      linarith
    -- Assemble.  Rewrite top = T everywhere and finish algebraically.
    rw [hslabR, hN, htop]
    ring
end ZetaRectangle
end BacklundTuring
end OverflowResidueRH

/-! ### Axiom audit -/

-- Confirm no new `sorryAx` is introduced by this construction.
#print axioms OverflowResidueRH.BacklundTuring.ZetaRectangle.rvMRectangleMainTermEvaluation
