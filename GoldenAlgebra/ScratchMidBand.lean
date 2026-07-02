/-
# ScratchMidBand — the mid-band Turing envelope `hTuring` on `[10,140]`

This file investigates and pushes the *mid-band* Turing log-envelope slot

  `hTuring : ∀ {z T u}, 10 ≤ T → T ≤ 140 → 0 < z.im →
      2*(1+|z.re|+z.im) ≤ T → T ≤ u →
        |finiteFluctuationPrimitive Dzero T0 u|
          ≤ (slabCD T).1 * log u + (slabCD T).2`

which is exactly the `log_envelope_from_T` field of
`FiniteFluctuationLogEnvelopeData` (rh §CCXXIV, rh.lean ~line 59965) and the
single remaining hard analytic input to the finite-fluctuation capstone
`XiPullbackAntiHerglotzTarget_of_finiteFluctuation_trueKernelTail`
(rh.lean ~line 60293).

---------------------------------------------------------------------------
## BRUTALLY HONEST AUDIT — what the SOS slab certs actually prove,
## and why they do NOT discharge `hTuring`.
---------------------------------------------------------------------------

The task framing was: "the SOS-slab / `zeros100ceil` route discharges
`hTuring`; wire the slab certificate data into `slabCD` to close it."
After reading the full chain in `rh.lean`, this framing is **incorrect**.
The SOS slab certificates feed a *parallel, downstream* branch — not the
`hTuring` envelope. Here is the actual logical structure.

### (A) What the SOS slab certs ARE (and they ARE fully proved in rh).

`SlabSimplePolyIneq zeros Tmin Tmax C D` (rh:47070) is the per-slab
polynomial inequality

  `closedFormSErrorBoundCD C D y T ≤ simpleCloudSum zeros x y
        + smoothTailRationalLowerBoundAbs x y T`

i.e. the *IBP/Stieltjes error envelope* `closedFormSErrorBoundCD` is
dominated by an explicit cloud-sum lower bound for the model margin.
All nine slabs over `zeros100ceil` are PROVED unconditionally and assembled
in `nineSlabSimpleCerts_zeros100ceil` (rh:53716, no `sorry`). They give
`hclosed_on_10_140_zeros100ceil` (rh:53739):

  `∃ C D, closedFormSErrorBoundCD C D z.im T ≤ -(M.model z).im`,

and via `slabCD` the deterministic
`hclosed_on_10_140_zeros100ceil_slabCD` (rh:53867):

  `closedFormSErrorBoundCD (slabCD T).1 (slabCD T).2 z.im T ≤ -(M.model z).im`.

The slab data files (`slab_certificates.lean`, `slab_80_140_data.lean`,
`GoldenAlgebra.SlabCertificates`) carry the per-slab `(Tmin,Tmax,C,D)`
table, the 50-zero list, and per-slab `margin/error` ratios. Their `(C,D)`
table is *exactly* `slabCD` (rh:53807). The "error" in those comments is
`closedFormSErrorBoundCD`; the "margin" is `-(model.im)`. So the data files
document the **(A) branch** (error ≤ model margin), which is already proved
in rh.

### (B) What `hTuring` IS — a DIFFERENT object, upstream of (A).

`closedFormSErrorBoundCD C D y T = 8·y·(C·log T + D)/T² + …` (rh:4218) is
the result of integrating the Cauchy kernel `|k| ≤ 8/u²` against an
*assumed* fluctuation envelope `|S(u)| ≤ C·log u + D`. The constants
`(C,D)` in `closedFormSErrorBoundCD` are literally the Turing-envelope
constants propagated through the kernel integral. So the real dependency
order is:

  `hTuring : |S(u)| ≤ C·log u + D`   (INPUT envelope — this file's target)
      │  IBP against Cauchy kernel (rh §CCVI/§CCX, PROVED)
      ▼
  `|error.im| ≤ closedFormSErrorBoundCD C D y T`   (PROVED machinery)
      │  slab certs (A)                              (PROVED)
      ▼
  `closedFormSErrorBoundCD ≤ -(model.im)`           (PROVED)

The slab certs sit *below* `hTuring`; they consume the same `(C,D)` but
PRESUPPOSE the envelope. They cannot produce it.

### (C) `hTuring` cannot even hold for the finite slab-data `Dzero`.

`S(u) = finiteFluctuationPrimitive Dzero T0 u
       = discreteCountingPrimitive Dzero T0 u − smoothCountingPrimitive T0 u`
(rh:55693), where `discreteCountingPrimitive D T0 u = Σ_{j<D.n, T0≤Z_j≤u} mult_j`
ranges over a **finite** index set `Finset.range D.n` (rh:55454), while
`smoothCountingPrimitive T0 u = ∫_{T0}^u ρ` grows like `u·log u`. Hence for
any *finite* `Dzero`, `S(u) → −∞`, and the bound
`|S(u)| ≤ 0·log u + 21/100` (the `T ≤ 12` slab, where `(slabCD T).1 = 0`)
is FALSE for large `u`. So `hTuring` is genuinely an *idealized* analytic
hypothesis about the TRUE (infinite) zero distribution, not something the
finite SOS data can witness.

### (D) rh.lean's OWN stated plan agrees.

The `BacklundTuring` namespace (rh:4299) names the deferred target
`concreteS_halfLogPlusHalf_bound_from_140` (rh:4316):
  `∀ u ≥ 140, |concreteS u| ≤ (1/2)·log u + 1/2`,
with the decomposition plan listed as the genuine analytic Turing method
(argument principle, ζ vertical-edge / Γ-factor / contour estimates,
Turing finite-interval certificate checker). rh explicitly says
"Do not state the final Backlund/Turing bound until all required lemmas
exist." It is OPEN by design, separate from the slab certs.

### CONCLUSION OF AUDIT.

`hTuring` is irreducibly the analytic Turing envelope on the zero-counting
fluctuation. The SOS slab certs do not, and cannot, discharge it. The most
honest, useful work here is therefore to **build the bridge** from the
realistic envelope structures (`TuringStyleSBound` / per-slab envelope) to
the EXACT `hTuring` shape, prove all the algebra that IS provable
(the `slabCD` lower/relationship lemmas and the envelope-monotonicity
reductions), and isolate the single irreducible residual as one named
hypothesis with an honest docstring. That is what follows.
---------------------------------------------------------------------------
-/

import rh

namespace OverflowResidueRH
namespace BacklundTuring
namespace ScratchMidBand

open OverflowResidueRH
open scoped BigOperators

/-! ## §1. Provable `slabCD` shape facts.

These are the algebraic facts about the deterministic `slabCD` selector
that ANY envelope-supplier must be measured against. They are all closed
unconditionally by `norm_num` after `split_ifs`. -/

/-- ⭐ **PROVED — `(slabCD T).1 ∈ {0, 1/2}`, so `(slabCD T).1 ≤ 1/2`.** -/
lemma slabCD_fst_le_half (T : ℝ) : (slabCD T).1 ≤ 1 / 2 := by
  unfold slabCD; split_ifs <;> norm_num

/-- ⭐ **PROVED — `(slabCD T).2 ≤ 49/20`** for every `T`. The largest `D`
in the table is the `[48,80]`/`[80,140]` value `49/20`. -/
lemma slabCD_snd_le_top (T : ℝ) : (slabCD T).2 ≤ 49 / 20 := by
  unfold slabCD; split_ifs <;> norm_num

/-- ⭐ **PROVED — both slab components are nonnegative.** (Mirrors the rh
lemmas `slabCD_fst_nonneg` / `slabCD_snd_nonneg`, restated locally so the
bridge below is self-contained.) -/
lemma slabCD_nonneg (T : ℝ) : 0 ≤ (slabCD T).1 ∧ 0 ≤ (slabCD T).2 := by
  constructor <;> · unfold slabCD; split_ifs <;> norm_num

/-- ⭐ **PROVED — the slab envelope is DOMINATED by the half-log-plus-half
envelope whenever `1 ≤ u`.** I.e. for any `u ≥ 1`,
`(slabCD T).1 · log u + (slabCD T).2 ≤ (1/2)·log u + 49/20`.

This is the monotone shape comparison that lets a single global envelope
constant feed every slab. Uses `(slabCD T).1 ≤ 1/2`, `log u ≥ 0` (from
`u ≥ 1`), and `(slabCD T).2 ≤ 49/20`. -/
lemma slab_envelope_le_global
    {T u : ℝ} (hu : 1 ≤ u) :
    (slabCD T).1 * Real.log u + (slabCD T).2
      ≤ (1 / 2 : ℝ) * Real.log u + 49 / 20 := by
  have hlog_nonneg : 0 ≤ Real.log u := Real.log_nonneg hu
  have h1 : (slabCD T).1 * Real.log u ≤ (1 / 2 : ℝ) * Real.log u :=
    mul_le_mul_of_nonneg_right (slabCD_fst_le_half T) hlog_nonneg
  have h2 : (slabCD T).2 ≤ 49 / 20 := slabCD_snd_le_top T
  linarith

/-! ## §2. The bridge: a global envelope ⟹ the per-slab `hTuring` shape.

KEY OBSERVATION about direction. `hTuring` requires the *upper* envelope
`|S u| ≤ (slabCD T).1·log u + (slabCD T).2`. The slab `(C,D)` constants are
SMALL (e.g. `C=0, D=21/100` on `[10,12]`). A *global* `(1/2)log u + 49/20`
envelope is LARGER than the slab envelope (`slab_envelope_le_global`), so a
global envelope does NOT imply the tighter per-slab one. The reduction must
go the other way: a *per-slab* envelope supplier is what `hTuring` needs.

We therefore phrase the bridge with the per-slab envelope as the named
hypothesis. This is the genuine, irreducible analytic content (the Turing
method on each height band), and we keep it as an honest hypothesis rather
than fabricating it. Everything around it is proved. -/

/-- 📦 **`PerSlabTuringEnvelope D T0`** — the honest, irreducible analytic
residual: the per-slab Turing log-envelope on the finite-fluctuation
primitive. This is EXACTLY `hTuring`, named as a structure so its status
(one open analytic obligation) is explicit and so the downstream bridge is
total.

It is NOT derivable from the SOS slab certs (see the file-header audit,
parts (B)/(C)): those certs are downstream of this envelope and presuppose
it. Discharging this is the `BacklundTuring` argument-principle / contour
program (rh §CXLIX-E), deferred in rh by design. -/
structure PerSlabTuringEnvelope
    (D : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ) : Prop where
  envelope :
    ∀ {z : ℂ} {T u : ℝ},
      10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      T ≤ u →
      |Phase1IBP.finiteFluctuationPrimitive D T0 u|
        ≤ (slabCD T).1 * Real.log u + (slabCD T).2

/-- 🌟 **PROVED — `PerSlabTuringEnvelope` is definitionally the `hTuring`
shape.** Trivial unfold; recorded so callers can pass a
`PerSlabTuringEnvelope` wherever rh wants the raw `∀ {z T u}, …` envelope. -/
theorem perSlabTuringEnvelope_to_hTuring
    {D : Phase1IBP.OrderedFluctuationMeasureData} {T0 : ℝ}
    (H : PerSlabTuringEnvelope D T0) :
    ∀ {z : ℂ} {T u : ℝ},
      10 ≤ T → T ≤ 140 → 0 < z.im →
      2 * (1 + |z.re| + z.im) ≤ T →
      T ≤ u →
      |Phase1IBP.finiteFluctuationPrimitive D T0 u|
        ≤ (slabCD T).1 * Real.log u + (slabCD T).2 :=
  fun h10 h140 hy hreg hTu => H.envelope h10 h140 hy hreg hTu

/-- 🌟🌟 **PROVED — `FiniteFluctuationLogEnvelopeData` from the per-slab
envelope.** Composes the bridge above with rh's
`finiteFluctuationLogEnvelopeData_of_turingBound` (rh:60239), which already
discharges the `derivative_integrable` field unconditionally (given
`0 < T0 ≤ 10`). So the ENTIRE `FiniteFluctuationLogEnvelopeData` reduces to
the single `PerSlabTuringEnvelope` residual. -/
theorem finiteFluctuationLogEnvelopeData_of_perSlab
    (D : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    (hT0_pos : 0 < T0) (hT0_le_10 : T0 ≤ 10)
    (H : PerSlabTuringEnvelope D T0) :
    FiniteFluctuationLogEnvelopeData D T0 :=
  finiteFluctuationLogEnvelopeData_of_turingBound
    D T0 hT0_pos hT0_le_10
    (perSlabTuringEnvelope_to_hTuring H)

/-- 🌟🌟🌟 **PROVED — finite-fluctuation capstone, gated only by the
per-slab envelope.** This threads `PerSlabTuringEnvelope` all the way into
`XiPullbackAntiHerglotzTarget_of_finiteFluctuation_trueKernelTail`
(rh:60293). Every slot except `PerSlabTuringEnvelope` is supplied by the
caller as the (already-developed) Model / decomposition / tail / cover data;
the mid-band Turing envelope is the lone analytic residual, isolated and
documented. -/
theorem xiPullbackAntiHerglotzTarget_of_perSlabEnvelope
    (D : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    (hT0_pos : 0 < T0) (hT0_le_10 : T0 ≤ 10)
    (H : PerSlabTuringEnvelope D T0)
    (Model : ActualCloudDensityModelData)
    (error : ℂ → ℂ)
    (hdecomp : ∀ z : ℂ,
        (∃ T : ℝ, 10 ≤ T ∧ T ≤ 140 ∧
          2 * (1 + |z.re| + z.im) ≤ T) →
        logDerivativeResponse XiPullback z = Model.M.model z + error z)
    (Dtail :
      TrueKernelTailData
        (fun u => Phase1IBP.finiteFluctuationPrimitive D T0 u)
        (realIBPFamilyData_of_finiteFluctuation_turingBound
          D T0 hT0_pos hT0_le_10 (perSlabTuringEnvelope_to_hTuring H))
        error)
    (Cover : LowHighBandCoverData) :
    XiPullbackAntiHerglotzTarget :=
  XiPullbackAntiHerglotzTarget_of_finiteFluctuation_trueKernelTail
    D T0 hT0_pos hT0_le_10 (perSlabTuringEnvelope_to_hTuring H)
    Model error hdecomp Dtail Cover

/-! ## §3. A constructive *sufficient condition* that IS finite/checkable.

The honest residual `PerSlabTuringEnvelope` is unbounded-`u`. But it factors
through a TWO-sided split that separates the genuinely-analytic tail
(`u` large) from a finite-band part. Concretely, the per-slab envelope is
implied by the *global half-log-plus-half* envelope on `S` PLUS the slab
constants dominating it — BUT, as noted in §2, the direction is wrong:
the global envelope is larger. So instead we record the correct, weaker
sufficient condition that turns `hTuring` into a `TuringStyleSBound`-style
hypothesis with the slab `(C,D)` taken at their *per-slab* values.

The point of this section: make explicit, as a PROVED reduction, that the
ONLY thing missing is a per-slab uniform envelope, and that ANY supplier of
the form "for each slab `[Tmin,Tmax]`, `|S u| ≤ C·log u + D` for all
`u ≥ Tmin`" already yields `PerSlabTuringEnvelope`. -/

/-- 📦 **`SlabwiseEnvelopeSupplier D T0`** — a per-slab envelope keyed to the
nine `slabCD` bands. Each field is the Turing bound on the corresponding
band, with the band's `(C,D)` from `slabCD`. This is the cleanest possible
restatement of the residual: nine independent analytic bounds, each a
genuine Turing estimate on its height band. -/
structure SlabwiseEnvelopeSupplier
    (D : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ) : Prop where
  band :
    ∀ {T u : ℝ}, 10 ≤ T → T ≤ 140 → T ≤ u →
      |Phase1IBP.finiteFluctuationPrimitive D T0 u|
        ≤ (slabCD T).1 * Real.log u + (slabCD T).2

/-- 🌟 **PROVED — `SlabwiseEnvelopeSupplier ⟹ PerSlabTuringEnvelope`.**
The slabwise supplier (which does not mention `z` at all) trivially
specializes to the `z`-indexed `hTuring` shape: the bound is uniform in `z`
once `T` is fixed in the admissible band. This shows the residual is purely
a `(T,u)` statement; the `z`-quantifiers in `hTuring` are inert. -/
theorem perSlabTuringEnvelope_of_slabwise
    {D : Phase1IBP.OrderedFluctuationMeasureData} {T0 : ℝ}
    (H : SlabwiseEnvelopeSupplier D T0) :
    PerSlabTuringEnvelope D T0 where
  envelope := by
    intro z T u h10 h140 _hy _hreg hTu
    exact H.band h10 h140 hTu

/-- 🌟🌟 **PROVED — capstone gated by the slabwise supplier.** The cleanest
statement of where we stand: GIVEN the nine per-band Turing envelopes
(`SlabwiseEnvelopeSupplier`), the full finite-fluctuation
`XiPullbackAntiHerglotzTarget` follows. The slabwise supplier is the
minimal, honest residual surface. -/
theorem xiPullbackAntiHerglotzTarget_of_slabwise
    (D : Phase1IBP.OrderedFluctuationMeasureData) (T0 : ℝ)
    (hT0_pos : 0 < T0) (hT0_le_10 : T0 ≤ 10)
    (H : SlabwiseEnvelopeSupplier D T0)
    (Model : ActualCloudDensityModelData)
    (error : ℂ → ℂ)
    (hdecomp : ∀ z : ℂ,
        (∃ T : ℝ, 10 ≤ T ∧ T ≤ 140 ∧
          2 * (1 + |z.re| + z.im) ≤ T) →
        logDerivativeResponse XiPullback z = Model.M.model z + error z)
    (Dtail :
      TrueKernelTailData
        (fun u => Phase1IBP.finiteFluctuationPrimitive D T0 u)
        (realIBPFamilyData_of_finiteFluctuation_turingBound
          D T0 hT0_pos hT0_le_10
          (perSlabTuringEnvelope_to_hTuring
            (perSlabTuringEnvelope_of_slabwise H)))
        error)
    (Cover : LowHighBandCoverData) :
    XiPullbackAntiHerglotzTarget :=
  xiPullbackAntiHerglotzTarget_of_perSlabEnvelope
    D T0 hT0_pos hT0_le_10 (perSlabTuringEnvelope_of_slabwise H)
    Model error hdecomp Dtail Cover

end ScratchMidBand
end BacklundTuring
end OverflowResidueRH
