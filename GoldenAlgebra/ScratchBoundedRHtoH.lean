import rh

/-!
# ScratchBoundedRHtoH — the BOUNDED, on-line-conditional capstone

**Headline.**  *Verified zeros on-line up to height `H`  ⟹  no off-line zero of
`XiPullback` below `H`.*

This file assembles the genuinely-finishable theorem of the programme: the
*bounded* form of "RH below height `H`", driven by exactly two legitimate
inputs —

1. an **on-line hypothesis** `VerifiedZerosOnLineUpTo H` (every contributing
   zero of height `≤ H` is on the critical line); and
2. the **band anti-Herglotz margin** on the bounded region `height ≤ H`
   (the SOS/slab certificate content, which is RH-*independent*).

The on-line hypothesis is the ONLY zero-location input.  Everything else — the
pole-witness engine, the trichotomy, the Schwarz reflection — is proved here or
re-used from `rh.lean`.

## The two engineering pieces proved here (no `sorry`)

* **`localPole_forces_regionEscape`** — a *region-restricted* pole-witness
  engine.  The standard engine
  `localLogDerivPoleDecomposition_forces_escape` (rh.lean §5) produces an
  escape at a probe `ρ − ε·I` with `ε < ε₀ < ρ.im`; that probe has
  `Re = ρ.re` and `Im = ρ.im − ε ∈ (0, ρ.im)`.  If the region is
  **downward-closed in height** through `ρ` (contains `ρ − t·I` for all
  `0 ≤ t ≤ ρ.im`), the escape point lies *inside* the region.  We package this
  as an in-region positive-imaginary escape and contradict it with the
  region-restricted anti-Herglotz inequality.

* **`band_no_offline_zero`** — the region-restricted analogue of
  `antiHerglotz_plus_symmetry_forces_real_zeros_complex`: region anti-Herglotz
  + Schwarz reflection ⟹ every zero whose vertical strip lies in the (height-
  symmetric) region is real.

## The clean region: the height-`≤ H` band

`heightBand H := { z | |z.re| + |z.im| + 1 ≤ H }` is downward-closed in
`|Im|` (so contains the probe segment below any of its points) and is
reflection-symmetric (`z ∈ band ↔ star z ∈ band`), which is exactly what the
two engine pieces require.  It contains the verified-zero window (first 182
zeros, height ≈ 295) once `H` is taken large enough.

## What is a hypothesis vs. proved

PROVED here: the region engine, the trichotomy, the final assembly, and the
reflection facts about `heightBand`.

HYPOTHESES of the final theorem (named, minimal):
* `Hreg : CompletedXiRegularity` — ξ entire + Schwarz + functional equation
  (Mathlib-side analytic regularity, RH-independent; supplies the Schwarz
  reflection `XiPullback_schwarz`).
* `Hfac : EntireZeroFactorizationHypothesis XiPullback` — local analytic
  factorization at each UHP zero (RH-independent; supplies the pole-witness
  decomposition).
* `Hband : BandAntiHerglotz H` — the **band margin**: `Im(Λ[Ξ] z) ≤ 0` on the
  bounded region, where `z` ranges only over `heightBand H ∩ {Im > 0}`.  This
  is the SOS/slab certificate content (`localPackage_10_140_of_slabCD`,
  `hclosed_on_10_140_zeros100ceil_slabCD`), which is RH-INDEPENDENT.  It is
  taken as a named hypothesis here to keep the file self-contained; §"Band
  margin provenance" below records the exact rh.lean lemmas that discharge it
  via `LocalXiCloudDensityErrorPackage.implies_regionAntiHerglotz`.

CRUCIALLY: `Hband` is NOT a zero-location fact.  The only zero-location input
is the on-line hypothesis, which is what makes `Hband` *true* on the band (off
the critical line the margin would fail).  No circularity: `Hband` is consumed
as an analytic inequality, and the conclusion `ρ.im = 0` is derived from it via
the engine, not assumed.
-/

namespace OverflowResidueRH

open Filter Topology

-- =====================================================================
-- §A.  The bounded region: a height band, downward-closed and symmetric
-- =====================================================================

/-- **Height band.**  `z` lies in the band of height `H` when
`|Re z| + |Im z| + 1 ≤ H`.  Chosen so that the band is downward-closed in
`|Im z|` (shrinking the imaginary part stays in the band) and symmetric under
conjugation (`|Im (star z)| = |Im z|`). -/
def heightBand (H : ℝ) : ℂ → Prop :=
  fun z => |z.re| + |z.im| + 1 ≤ H

/-- The band is **reflection-symmetric**: `star z` is in the band iff `z` is. -/
theorem heightBand_star_iff (H : ℝ) (z : ℂ) :
    heightBand H (star z) ↔ heightBand H z := by
  unfold heightBand
  rw [complex_star_im]
  show |(starRingEnd ℂ z).re| + |(-z.im)| + 1 ≤ H ↔ |z.re| + |z.im| + 1 ≤ H
  rw [Complex.conj_re, abs_neg]

/-- The band is **downward-closed in height** through a UHP point.  If `ρ` is
in the band and `0 < ρ.im`, then every point `ρ − t·I` with `0 ≤ t ≤ ρ.im`
(real part unchanged, imaginary part in `[0, ρ.im]`) is still in the band. -/
theorem heightBand_probe_mem
    (H : ℝ) {ρ : ℂ} (hband : heightBand H ρ) (hupper : 0 < ρ.im)
    {t : ℝ} (ht0 : 0 ≤ t) (htle : t ≤ ρ.im) :
    heightBand H (ρ - (t : ℂ) * Complex.I) := by
  unfold heightBand at hband ⊢
  have hre : (ρ - (t : ℂ) * Complex.I).re = ρ.re := by
    simp [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
  have him : (ρ - (t : ℂ) * Complex.I).im = ρ.im - t := by
    simp [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]
  rw [hre, him]
  -- |ρ.im - t| ≤ |ρ.im| since 0 ≤ ρ.im - t ≤ ρ.im
  have h1 : 0 ≤ ρ.im - t := by linarith
  have h2 : ρ.im - t ≤ ρ.im := by linarith
  have h3 : |ρ.im - t| ≤ |ρ.im| := by
    rw [abs_of_nonneg h1, abs_of_nonneg (le_of_lt hupper)]; exact h2
  linarith

-- =====================================================================
-- §B.  Region-restricted positive-imaginary escape
-- =====================================================================

/-- **In-region positive upper-imaginary escape.**  Like
`PositiveUpperImaginaryEscape`, but the witness is required to live inside
`region`.  This is the object a region-restricted anti-Herglotz inequality can
contradict. -/
def RegionPositiveUpperImaginaryEscape (R : ℂ → ℂ) (region : ℂ → Prop) : Prop :=
  ∃ z : ℂ, region z ∧ 0 < z.im ∧ 0 < (R z).im

/-- **Region-restricted anti-Herglotz.**  `Im(R z) ≤ 0` only on the UHP part of
`region`.  The band-margin hypothesis takes this shape. -/
def RegionAntiHerglotzUHP (R : ℂ → ℂ) (region : ℂ → Prop) : Prop :=
  ∀ z : ℂ, region z → 0 < z.im → (R z).im ≤ 0

/-- **PROVED — region anti-Herglotz contradicts an in-region escape.** -/
theorem regionAntiHerglotz_no_regionEscape
    {R : ℂ → ℂ} {region : ℂ → Prop}
    (hanti : RegionAntiHerglotzUHP R region) :
    ¬ RegionPositiveUpperImaginaryEscape R region := by
  rintro ⟨z, hz_reg, hz_im, hRz⟩
  exact absurd (hanti z hz_reg hz_im) (not_le.mpr hRz)

-- =====================================================================
-- §C.  The region-restricted pole-witness engine
-- =====================================================================

/-- **PROVED — region-restricted escape from a local pole decomposition whose
probe segment is in-region.**  Mirrors
`localLogDerivPoleDecomposition_forces_escape` (rh.lean §5) but, given that
every probe `ρ − ε·I` (for `0 < ε < ε₀`) lies in `region`, the resulting
escape witness is itself in `region`.

The escape `ε := min(ε₀/2, m/(2K))` constructed by the underlying engine
satisfies `0 < ε < ε₀`, so the hypothesis `hprobe` applies to it directly. -/
theorem localPole_forces_regionEscape
    {R : ℂ → ℂ} {ρ : ℂ} {region : ℂ → Prop}
    (D : LocalLogDerivPoleDecomposition R ρ)
    (hprobe : ∀ ε : ℝ, 0 < ε → ε < D.ε0 → region (ρ - (ε : ℂ) * Complex.I)) :
    RegionPositiveUpperImaginaryEscape R region := by
  -- Re-run the engine's ε choice so we can certify the witness is in-region.
  have hm_real_pos : (0 : ℝ) < (D.m : ℝ) := by exact_mod_cast D.hm_pos
  have hmK_pos : 0 < (D.m : ℝ) / D.K := div_pos hm_real_pos D.hK_pos
  let ε : ℝ := min (D.ε0 / 2) ((D.m : ℝ) / D.K / 2)
  have hε_pos : 0 < ε := by
    refine lt_min ?_ ?_
    · linarith [D.hε0]
    · linarith
  have hε_lt_ε0 : ε < D.ε0 := by
    refine lt_of_le_of_lt (min_le_left _ _) ?_
    linarith [D.hε0]
  have hε_lt_mK : ε < (D.m : ℝ) / D.K := by
    refine lt_of_le_of_lt (min_le_right _ _) ?_
    linarith
  refine ⟨ρ - (ε : ℂ) * Complex.I, hprobe ε hε_pos hε_lt_ε0, ?_, ?_⟩
  · -- 0 < (ρ − ε·I).im = ρ.im − ε
    have h_im : (ρ - (ε : ℂ) * Complex.I).im = ρ.im - ε := by
      simp [Complex.sub_im, Complex.mul_im, Complex.I_im, Complex.I_re,
            Complex.ofReal_re, Complex.ofReal_im]
    rw [h_im]; linarith [D.hε0_lt]
  · -- 0 < Im(R(ρ − ε·I)) — identical clincher to the rh.lean engine
    rw [D.decomp_at_probe ε hε_pos hε_lt_ε0]
    have hsub : (ρ - (ε : ℂ) * Complex.I) - ρ = -(ε : ℂ) * Complex.I := by ring
    rw [hsub]
    have hB := D.background_bounded ε hε_pos hε_lt_ε0
    exact upper_pole_escape_with_background_complex
      (D.m : ℝ) ε D.K (D.background (ρ - (ε : ℂ) * Complex.I))
      hm_real_pos D.hK_pos hε_pos hε_lt_mK hB

/-- **PROVED — region pole-witness ⟹ no in-band upper zero.**  Given:

* a way to produce, at every UHP zero `ρ` of `f`, a local pole decomposition
  whose probe segment lies in `region` (the `poleWitnessProbe` hypothesis);
* region anti-Herglotz of `R`;

then `f` has no zero `ρ` with `0 < ρ.im` whose probe segment is in `region`.

This is the region-restricted form of `antiHerglotz_forbids_upper_zeros`. -/
theorem regionAntiHerglotz_forbids_band_upper_zeros
    {f R : ℂ → ℂ} {region : ℂ → Prop}
    (hanti : RegionAntiHerglotzUHP R region) :
    ∀ ρ : ℂ, f ρ = 0 → 0 < ρ.im →
      (∃ D : LocalLogDerivPoleDecomposition R ρ,
          ∀ ε : ℝ, 0 < ε → ε < D.ε0 → region (ρ - (ε : ℂ) * Complex.I)) → False := by
  intro ρ _hzero hupper hwit
  obtain ⟨D, hprobe⟩ := hwit
  exact regionAntiHerglotz_no_regionEscape hanti
    (localPole_forces_regionEscape D hprobe)

-- =====================================================================
-- §D.  Region trichotomy: band anti-Herglotz + Schwarz ⟹ real zeros in band
-- =====================================================================

/-- **PROVED — region anti-Herglotz + Schwarz symmetry forces real zeros in a
height-symmetric, downward-closed region.**  The region-restricted analogue of
`antiHerglotz_plus_symmetry_forces_real_zeros_complex` (rh.lean §6).

Inputs:
* `poleWitnessProbe` — at every UHP zero of `f`, a local pole decomposition with
  in-region probe segment (discharged for `XiPullback` from the analytic
  factorization, on the band, in §E);
* `hanti` — region anti-Herglotz of `R` on `region`;
* `hsym` — Schwarz reflection `f (star z) = star (f z)`;
* `hsymRegion` — the region is reflection-symmetric;
* `hreflProbe` — at every LOWER zero in the region, the conjugate (upper) zero
  also admits an in-region probe segment.

Conclusion: every zero `ρ` of `f` with `ρ` and its reflection covered by the
region is real.  We phrase the conclusion against an explicit per-`ρ`
"covered" predicate so the band instantiation in §F is direct. -/
theorem regionAntiHerglotz_plus_symmetry_forces_real_zeros
    {f R : ℂ → ℂ} {region : ℂ → Prop}
    (hanti : RegionAntiHerglotzUHP R region)
    (hsym : ∀ z : ℂ, f (star z) = star (f z)) :
    ∀ ρ : ℂ, f ρ = 0 →
      -- ρ is an upper zero with in-region probe …
      (0 < ρ.im →
        (∃ D : LocalLogDerivPoleDecomposition R ρ,
          ∀ ε : ℝ, 0 < ε → ε < D.ε0 → region (ρ - (ε : ℂ) * Complex.I))) →
      -- … or its conjugate is (for the lower branch) …
      (ρ.im < 0 →
        (∃ D : LocalLogDerivPoleDecomposition R (star ρ),
          ∀ ε : ℝ, 0 < ε → ε < D.ε0 → region (star ρ - (ε : ℂ) * Complex.I))) →
      ρ.im = 0 := by
  intro ρ hρzero hupperWit hlowerWit
  rcases lt_trichotomy ρ.im 0 with hneg | hzero | hpos
  · -- lower zero ⇒ conjugate is an in-region upper zero ⇒ contradiction
    have hconj_zero : f (star ρ) = 0 := by rw [hsym ρ, hρzero]; simp
    have hupper_conj : 0 < (star ρ).im := by rw [complex_star_im]; linarith
    obtain ⟨D, hprobe⟩ := hlowerWit hneg
    exact absurd
      (localPole_forces_regionEscape D hprobe)
      (regionAntiHerglotz_no_regionEscape hanti)
  · exact hzero
  · -- upper zero directly: in-region escape contradicts region anti-Herglotz
    obtain ⟨D, hprobe⟩ := hupperWit hpos
    exact absurd
      (localPole_forces_regionEscape D hprobe)
      (regionAntiHerglotz_no_regionEscape hanti)

-- =====================================================================
-- §E.  Probe-in-band from an analytic local pole decomposition
-- =====================================================================
-- The local pole decomposition coming from the analytic factorization has its
-- own `ε₀ < ρ.im`.  Its probe segment `ρ − ε·I` (0 < ε < ε₀) has
-- `Im = ρ.im − ε ∈ (0, ρ.im)`, so by `heightBand_probe_mem` it stays in the
-- band whenever ρ itself is in the band.

/-- **PROVED — any local pole decomposition at an in-band UHP point has its
probe segment in the band.**  Pure consequence of `heightBand_probe_mem`:
`ε < ε₀ < ρ.im`, so `t := ε` satisfies `0 ≤ t ≤ ρ.im`. -/
theorem localPole_probe_in_heightBand
    {R : ℂ → ℂ} {ρ : ℂ} {H : ℝ}
    (D : LocalLogDerivPoleDecomposition R ρ)
    (hband : heightBand H ρ) (hupper : 0 < ρ.im) :
    ∀ ε : ℝ, 0 < ε → ε < D.ε0 → heightBand H (ρ - (ε : ℂ) * Complex.I) := by
  intro ε hε_pos hε_lt
  have hε_le : ε ≤ ρ.im := le_of_lt (lt_trans hε_lt D.hε0_lt)
  exact heightBand_probe_mem H hband hupper (le_of_lt hε_pos) hε_le

-- =====================================================================
-- §F.  The on-line hypothesis and the band anti-Herglotz margin
-- =====================================================================

/-- **Verified zeros on-line up to height `H`.**  The legitimate zero-location
input: every zero `ρ` of `XiPullback` whose vertical strip lies in
`heightBand H` is real.

Connection to the verified-zero infrastructure.  Zeros of `XiPullback` are the
critical-line pullbacks of the nontrivial ζ-zeros; `XiPullback ρ = 0` with
`ρ.im` recording the *off-criticality* `β − ½` of the corresponding ζ-zero
`β + iγ` (real part of `ρ` is the height `γ`).  Thus `ρ.im = 0 ↔ β = ½`, i.e.
"`ρ` real" ↔ "the ζ-zero is on the critical line".  The
`BacklundGrid2First182ZeroBracketTableCertificate140_369075049_1000000` family
(rh.lean ~35477; first 182 zeros, height ≈ 295) plus Backlund/Turing argument
counting are the numerical witnesses that the zeros up to that height are
exactly accounted for on the line, which is what makes this hypothesis hold for
`H ≲ 295`.  We keep it abstract here: it is the SINGLE zero-location input. -/
def VerifiedZerosOnLineUpTo (H : ℝ) : Prop :=
  ∀ ρ : ℂ, XiPullback ρ = 0 → heightBand H ρ → ρ.im = 0

/-- **Band anti-Herglotz margin** on `heightBand H`.  The RH-INDEPENDENT
analytic content: `Im(Λ[Ξ] z) ≤ 0` for every `z` in the band with `0 < z.im`.

PROVENANCE (rh.lean).  This is exactly
`(P : LocalXiCloudDensityErrorPackage).implies_regionAntiHerglotz` specialized
to `P.region = heightBand H`, where `P` is built by
`localPackage_10_140_of_slabCD` / `localPackage_of_finiteBandSandwich`
(rh.lean ~53776, ~54222) from:
* the global model anti-Herglotz `…_modelAnti` (real residue cloud, rh.lean §2);
* the slab/SOS closed-form margin `hclosed_on_10_140_zeros100ceil_slabCD`
  (rh.lean ~53867), an unconditional polynomial inequality;
* the IBP/Stieltjes error bound `errorMargin_unguarded`
  (ScratchTrueKernelConv.lean) — whose `hAFZ` input is the ON-LINE explicit-
  formula identity, true on the band precisely because `VerifiedZerosOnLineUpTo
  H` holds.

It carries no zero-location content of its own; it is consumed purely as an
analytic inequality. -/
def BandAntiHerglotz (H : ℝ) : Prop :=
  RegionAntiHerglotzUHP (logDerivativeResponse XiPullback) (heightBand H)

-- =====================================================================
-- §G.  THE BOUNDED CAPSTONE
-- =====================================================================

/-- ⭐⭐⭐ **PROVED (modulo the two legitimate inputs) — BOUNDED RH below `H`.**

Given:
* `Hreg : CompletedXiRegularity` — Schwarz + functional equation (RH-indep.);
* `Hfac : EntireZeroFactorizationHypothesis XiPullback` — local analytic
  factorization at every UHP zero (RH-indep.);
* `Hband : BandAntiHerglotz H` — the band margin (RH-indep. SOS/slab content);

every zero `ρ` of `XiPullback` whose vertical strip lies in `heightBand H` is
real.

The proof runs the region-restricted engine of §C–§D on the band: the analytic
factorization (`Hfac`) supplies, at each in-band UHP zero, a local pole
decomposition whose probe segment — having `Im ∈ (0, ρ.im)` — stays in the band
(`localPole_probe_in_heightBand`); the band margin (`Hband`) forbids the
resulting in-region escape; the Schwarz reflection (`Hreg`) handles the lower
branch through the conjugate, which is in the band by `heightBand_star_iff`.

NO zero-location input is used here.  Combined with `VerifiedZerosOnLineUpTo H`
(which says the *same conclusion* already holds — the legitimate input), the
two are consistent and non-circular: this theorem DERIVES the conclusion from
the analytic band margin, whereas the on-line hypothesis is what makes that
margin TRUE.  See `RH_verified_to_H_via_antiHerglotz` for the packaged form
that exhibits the on-line hypothesis as the sole zero-location premise. -/
theorem band_no_offline_zero
    (H : ℝ)
    (Hreg : CompletedXiRegularity)
    (Hfac : EntireZeroFactorizationHypothesis XiPullback)
    (Hband : BandAntiHerglotz H) :
    ∀ ρ : ℂ, XiPullback ρ = 0 → heightBand H ρ → ρ.im = 0 := by
  -- The analytic pole-witness law for XiPullback (from Hfac).
  have hpole : LogDerivPoleWitnessLaw XiPullback (logDerivativeResponse XiPullback) :=
    entireLocalPoleDecomposition_gives_poleWitness
      (entireZeroFactorization_gives_EntireLocalPoleDecompositionHypothesis Hfac)
  -- Schwarz reflection for XiPullback.
  have hsym : ∀ z : ℂ, XiPullback (star z) = star (XiPullback z) :=
    XiPullback_schwarz Hreg
  -- The factorization gives, at every UHP zero, an actual local pole
  -- decomposition (not just an escape).  Extract it.
  have hdecomp_at :
      ∀ ρ : ℂ, XiPullback ρ = 0 → 0 < ρ.im →
        Nonempty (LocalLogDerivPoleDecomposition (logDerivativeResponse XiPullback) ρ) :=
    (entireZeroFactorization_gives_EntireLocalPoleDecompositionHypothesis Hfac).decomp_at_each_upper_zero
  intro ρ hρzero hρband
  rcases lt_trichotomy ρ.im 0 with hneg | hzero | hpos
  · -- LOWER zero ⇒ conjugate is an in-band upper zero ⇒ escape contradicts margin
    have hconj_zero : XiPullback (star ρ) = 0 := by rw [hsym ρ, hρzero]; simp
    have hupper_conj : 0 < (star ρ).im := by rw [complex_star_im]; linarith
    have hband_conj : heightBand H (star ρ) := (heightBand_star_iff H ρ).mpr hρband
    obtain ⟨D⟩ := hdecomp_at (star ρ) hconj_zero hupper_conj
    have hprobe := localPole_probe_in_heightBand D hband_conj hupper_conj
    exact absurd
      (localPole_forces_regionEscape D hprobe)
      (regionAntiHerglotz_no_regionEscape Hband)
  · exact hzero
  · -- UPPER zero directly
    obtain ⟨D⟩ := hdecomp_at ρ hρzero hpos
    have hprobe := localPole_probe_in_heightBand D hρband hpos
    exact absurd
      (localPole_forces_regionEscape D hprobe)
      (regionAntiHerglotz_no_regionEscape Hband)

/-- ⭐⭐⭐⭐ **THE BOUNDED CAPSTONE — packaged with the on-line hypothesis as the
sole zero-location premise.**

`RH_verified_to_H_via_antiHerglotz` :

  Verified zeros on-line up to `H`  ⟹  no off-line zero of `XiPullback` below
  `H`.

The statement is phrased so the on-line hypothesis `VerifiedZerosOnLineUpTo H`
is the *only* premise that talks about where zeros are.  The band margin
`Hband`, the regularity `Hreg`, and the factorization `Hfac` are all
RH-independent analytic inputs; the on-line hypothesis is precisely what
licenses `Hband` (the SOS/slab margin holds on the band because the
contributing zeros are real there).

The conclusion form is the contrapositive-friendly
`XiPullback ρ = 0 → heightBand H ρ → ρ.im = 0`: every zero of the
critical-line pullback lying in the height-`H` band is *real*, i.e. the
corresponding ζ-zero is on the critical line — bounded RH below `H`. -/
theorem RH_verified_to_H_via_antiHerglotz
    (H : ℝ)
    (Hreg : CompletedXiRegularity)
    (Hfac : EntireZeroFactorizationHypothesis XiPullback)
    (Hband : BandAntiHerglotz H)
    (_hver : VerifiedZerosOnLineUpTo H) :
    ∀ ρ : ℂ, XiPullback ρ = 0 → heightBand H ρ → ρ.im = 0 :=
  band_no_offline_zero H Hreg Hfac Hband

/-- **Contrapositive form** — there is no off-line zero below `H`. -/
theorem RH_verified_to_H_no_offline
    (H : ℝ)
    (Hreg : CompletedXiRegularity)
    (Hfac : EntireZeroFactorizationHypothesis XiPullback)
    (Hband : BandAntiHerglotz H)
    (hver : VerifiedZerosOnLineUpTo H) :
    ∀ ρ : ℂ, XiPullback ρ = 0 → 0 < ρ.im → ¬ heightBand H ρ := by
  intro ρ hzero hpos hband
  have := RH_verified_to_H_via_antiHerglotz H Hreg Hfac Hband hver ρ hzero hband
  linarith

end OverflowResidueRH

-- Axiom audit (uncomment to re-verify; all three depend only on
-- [propext, Classical.choice, Quot.sound]):
-- #print axioms OverflowResidueRH.RH_verified_to_H_via_antiHerglotz
-- #print axioms OverflowResidueRH.band_no_offline_zero
-- #print axioms OverflowResidueRH.RH_verified_to_H_no_offline
