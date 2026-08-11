import stoch_to_det.Envelope
import Mathlib.Analysis.Convex.Integral

/-!
# Arbitrary measurable posterior latents

The finite `Latent` structure remains unchanged.  A `GeneralLatent` is a
probability measure on an arbitrary measurable latent alphabet together with
a coordinatewise-measurable family of finite posterior laws.  Its barycenter
is the prescribed law `p`.

The central theorem of this module is exact finite compression: integrating
the compact graph of `Phi` produces a point of its finite convex hull, so a
finite `Latent` has exactly the same score.  No entropy of the latent alphabet
is used.
-/

universe u

namespace stoch_to_det

open MeasureTheory

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- A possibly infinite latent, represented by its prior and its posterior
laws of `(X,Y)`. -/
structure GeneralLatent (p : α × β → ℝ)
    (ι : Type u) [MeasurableSpace ι] where
  prior : Measure ι
  prior_isProbability : IsProbabilityMeasure prior
  posterior : ι → (α × β → ℝ)
  posterior_measurable :
    ∀ z : α × β, Measurable (fun v => posterior v z)
  posterior_isPMF : ∀ v : ι, IsPMF (posterior v)
  barycenter : ∀ z : α × β,
    ∫ v, posterior v z ∂prior = p z

/-- Alternate name emphasizing that this is the posterior-mixture layer. -/
abbrev PosteriorLatent (p : α × β → ℝ)
    (ι : Type u) [MeasurableSpace ι] := GeneralLatent p ι

namespace GeneralLatent

variable {p : α × β → ℝ}
variable {ι : Type u} [MeasurableSpace ι]

/-- The general-latent representation is already the posterior-mixture layer,
so conversion to `PosteriorLatent` is exact and carries no data change. -/
def toPosterior (V : GeneralLatent p ι) : PosteriorLatent p ι := V

/-- `I(X;Y | V)`, defined entirely through finite posterior laws. -/
noncomputable def IxyGiven (V : GeneralLatent p ι) : ℝ :=
  ∫ v, Ixy (V.posterior v) ∂V.prior

/-- `I(V;X | Y)`, without an `H(V)` term. -/
noncomputable def IvxGivenY (V : GeneralLatent p ι) : ℝ :=
  condH (fun z : α × β => z.1) (fun z => z.2) p -
    ∫ v, condH (fun z : α × β => z.1) (fun z => z.2)
      (V.posterior v) ∂V.prior

/-- `I(V;Y | X)`, without an `H(V)` term. -/
noncomputable def IvyGivenX (V : GeneralLatent p ι) : ℝ :=
  condH (fun z : α × β => z.2) (fun z => z.1) p -
    ∫ v, condH (fun z : α × β => z.2) (fun z => z.1)
      (V.posterior v) ∂V.prior

/-- The generalized stochastic-latent score. -/
noncomputable def infoScore (V : GeneralLatent p ι) : ℝ :=
  V.IxyGiven + V.IvxGivenY + V.IvyGivenX

/-- The integrated envelope payoff. -/
noncomputable def payoff (V : GeneralLatent p ι) : ℝ :=
  ∫ v, Phi (V.posterior v) ∂V.prior

theorem posterior_measurable_map (V : GeneralLatent p ι) :
    Measurable V.posterior :=
  measurable_pi_lambda _ V.posterior_measurable

private noncomputable def continuousIxy (q : α × β → ℝ) : ℝ :=
  continuousEntropy (push Prod.fst q) +
    continuousEntropy (push Prod.snd q) - continuousEntropy q

private noncomputable def continuousHxGivenY (q : α × β → ℝ) : ℝ :=
  continuousEntropy q - continuousEntropy (push Prod.snd q)

private noncomputable def continuousHyGivenX (q : α × β → ℝ) : ℝ :=
  continuousEntropy q - continuousEntropy (push Prod.fst q)

private lemma continuous_continuousIxy :
    Continuous (continuousIxy : (α × β → ℝ) → ℝ) := by
  unfold continuousIxy
  exact ((continuous_continuousEntropy.comp (continuous_push_map Prod.fst)).add
    (continuous_continuousEntropy.comp (continuous_push_map Prod.snd))).sub
      continuous_continuousEntropy

private lemma continuous_continuousHxGivenY :
    Continuous (continuousHxGivenY : (α × β → ℝ) → ℝ) := by
  unfold continuousHxGivenY
  exact continuous_continuousEntropy.sub
    (continuous_continuousEntropy.comp (continuous_push_map Prod.snd))

private lemma continuous_continuousHyGivenX :
    Continuous (continuousHyGivenX : (α × β → ℝ) → ℝ) := by
  unfold continuousHyGivenX
  exact continuous_continuousEntropy.sub
    (continuous_continuousEntropy.comp (continuous_push_map Prod.fst))

private lemma Hvar_id_general {γ : Type*} [Fintype γ] [DecidableEq γ]
    {q : γ → ℝ} (hq : IsPMF q) :
    Hvar (fun z : γ => z) q = H q := by
  unfold Hvar
  change H (push (Equiv.refl γ) q) = H q
  exact H_push_equiv (Equiv.refl γ) q hq

lemma condH_fst_snd_eq {q : α × β → ℝ} (hq : IsPMF q) :
    condH (fun z : α × β => z.1) (fun z => z.2) q =
      H q - H (mY q) := by
  unfold condH
  have hid := Hvar_id_general hq
  change Hvar (fun z : α × β => (z.1, z.2)) q - H (mY q) = _
  simpa using congrArg (fun x => x - H (mY q)) hid

lemma condH_snd_fst_eq {q : α × β → ℝ} (hq : IsPMF q) :
    condH (fun z : α × β => z.2) (fun z => z.1) q =
      H q - H (mX q) := by
  unfold condH
  have hpair : Hvar (fun z : α × β => (z.2, z.1)) q = H q := by
    calc
      Hvar (fun z : α × β => (z.2, z.1)) q =
          Hvar (fun z : α × β => z) q := by
        have he : (fun z : α × β => (z.2, z.1)) =
            fun z => (Equiv.prodComm α β) z := by
          funext z
          rcases z with ⟨x, y⟩
          rfl
        rw [he]
        exact Hvar_equiv hq (fun z : α × β => z)
          (Equiv.prodComm α β)
      _ = H q := Hvar_id_general hq
  change Hvar (fun z : α × β => (z.2, z.1)) q - H (mX q) = _
  rw [hpair]

private lemma Ixy_eq_continuousIxy {q : α × β → ℝ} (hq : IsPMF q) :
    Ixy q = continuousIxy q := by
  unfold Ixy continuousIxy
  rw [H_eq_continuousEntropy hq,
    H_eq_continuousEntropy (isPMF_push hq : IsPMF (mX q)),
    H_eq_continuousEntropy (isPMF_push hq : IsPMF (mY q))]

private lemma condH_fst_snd_eq_continuous {q : α × β → ℝ}
    (hq : IsPMF q) :
    condH (fun z : α × β => z.1) (fun z => z.2) q =
      continuousHxGivenY q := by
  rw [condH_fst_snd_eq hq]
  unfold continuousHxGivenY
  rw [H_eq_continuousEntropy hq,
    H_eq_continuousEntropy (isPMF_push hq : IsPMF (mY q))]

private lemma condH_snd_fst_eq_continuous {q : α × β → ℝ}
    (hq : IsPMF q) :
    condH (fun z : α × β => z.2) (fun z => z.1) q =
      continuousHyGivenX q := by
  rw [condH_snd_fst_eq hq]
  unfold continuousHyGivenX
  rw [H_eq_continuousEntropy hq,
    H_eq_continuousEntropy (isPMF_push hq : IsPMF (mX q))]

/-- A continuous functional of the posterior is integrable, since all
posteriors lie in the compact finite PMF simplex. -/
theorem integrable_continuous_comp (V : GeneralLatent p ι)
    (g : (α × β → ℝ) → ℝ) (hg : Continuous g) :
    Integrable (fun v => g (V.posterior v)) V.prior := by
  letI : IsProbabilityMeasure V.prior := V.prior_isProbability
  have hcompact : IsCompact (g '' (pmfSet : Set (α × β → ℝ))) :=
    isCompact_pmfSet.image hg
  obtain ⟨C, hC⟩ := hcompact.isBounded.exists_norm_le
  apply Integrable.of_bound
    (hg.measurable.comp V.posterior_measurable_map).aestronglyMeasurable C
  exact ae_of_all _ fun v =>
    hC (g (V.posterior v)) ⟨V.posterior v, V.posterior_isPMF v, rfl⟩

lemma integrable_IxyGiven_integrand (V : GeneralLatent p ι) :
    Integrable (fun v => Ixy (V.posterior v)) V.prior := by
  have h := V.integrable_continuous_comp continuousIxy continuous_continuousIxy
  refine h.congr (ae_of_all _ fun v => ?_)
  exact (Ixy_eq_continuousIxy (V.posterior_isPMF v)).symm

lemma integrable_HxGivenY_integrand (V : GeneralLatent p ι) :
    Integrable
      (fun v => condH (fun z : α × β => z.1) (fun z => z.2)
        (V.posterior v)) V.prior := by
  have h := V.integrable_continuous_comp continuousHxGivenY
    continuous_continuousHxGivenY
  refine h.congr (ae_of_all _ fun v => ?_)
  exact (condH_fst_snd_eq_continuous (V.posterior_isPMF v)).symm

lemma integrable_HyGivenX_integrand (V : GeneralLatent p ι) :
    Integrable
      (fun v => condH (fun z : α × β => z.2) (fun z => z.1)
        (V.posterior v)) V.prior := by
  have h := V.integrable_continuous_comp continuousHyGivenX
    continuous_continuousHyGivenX
  refine h.congr (ae_of_all _ fun v => ?_)
  exact (condH_snd_fst_eq_continuous (V.posterior_isPMF v)).symm

lemma integrable_payoff_integrand (V : GeneralLatent p ι) :
    Integrable (fun v => Phi (V.posterior v)) V.prior := by
  have h := V.integrable_continuous_comp continuousPhi continuous_continuousPhi
  refine h.congr (ae_of_all _ fun v => ?_)
  exact (Phi_eq_continuousPhi (V.posterior_isPMF v)).symm

private lemma posterior_pointwise_ledger (V : GeneralLatent p ι) (v : ι) :
    Ixy (V.posterior v) -
        condH (fun z : α × β => z.1) (fun z => z.2) (V.posterior v) -
        condH (fun z : α × β => z.2) (fun z => z.1) (V.posterior v) =
      -Phi (V.posterior v) := by
  rw [condH_fst_snd_eq (V.posterior_isPMF v),
    condH_snd_fst_eq (V.posterior_isPMF v)]
  unfold Ixy Phi
  ring

/-- Integral decomposition of the generalized information score. -/
theorem infoScore_eq_Psi_sub_payoff (hp : IsPMF p)
    (V : GeneralLatent p ι) :
    V.infoScore = Psi p - V.payoff := by
  have hi := V.integrable_IxyGiven_integrand
  have hx := V.integrable_HxGivenY_integrand
  have hy := V.integrable_HyGivenX_integrand
  have hphi := V.integrable_payoff_integrand
  have hfixed :
      condH (fun z : α × β => z.1) (fun z => z.2) p +
        condH (fun z : α × β => z.2) (fun z => z.1) p = Psi p := by
    rw [condH_fst_snd_eq hp, condH_snd_fst_eq hp]
    unfold Psi
    ring
  have hintLedger :
      (∫ v, Ixy (V.posterior v) ∂V.prior) -
          (∫ v, condH (fun z : α × β => z.1) (fun z => z.2)
            (V.posterior v) ∂V.prior) -
          (∫ v, condH (fun z : α × β => z.2) (fun z => z.1)
            (V.posterior v) ∂V.prior) =
        -(∫ v, Phi (V.posterior v) ∂V.prior) := by
    calc
      _ = ∫ v, (Ixy (V.posterior v) -
            condH (fun z : α × β => z.1) (fun z => z.2) (V.posterior v)) -
            condH (fun z : α × β => z.2) (fun z => z.1) (V.posterior v)
          ∂V.prior := by
        symm
        calc
          _ = (∫ v, Ixy (V.posterior v) -
                condH (fun z : α × β => z.1) (fun z => z.2)
                  (V.posterior v) ∂V.prior) -
              ∫ v, condH (fun z : α × β => z.2) (fun z => z.1)
                (V.posterior v) ∂V.prior :=
            integral_sub (hi.sub hx) hy
          _ = _ := by rw [integral_sub hi hx]
      _ = ∫ v, -Phi (V.posterior v) ∂V.prior := by
        apply integral_congr_ae
        exact ae_of_all _ fun v => V.posterior_pointwise_ledger v
      _ = -(∫ v, Phi (V.posterior v) ∂V.prior) := by
        rw [integral_neg]
  unfold infoScore IxyGiven IvxGivenY IvyGivenX payoff
  linarith

/-- The score is, by definition, the three requested information terms. -/
theorem score_eq_info_sum (V : GeneralLatent p ι) :
    V.infoScore = V.IxyGiven + V.IvxGivenY + V.IvyGivenX := rfl

/-! ### Exact finite compression -/

/-- Every measurable posterior latent has a finite latent with exactly the
same score. -/
theorem exists_finite_score_eq (hp : IsPMF p) (V : GeneralLatent p ι) :
    ∃ W : Latent p, W.score = V.infoScore := by
  letI : IsProbabilityMeasure V.prior := V.prior_isProbability
  let F : ι → (α × β → ℝ) × ℝ := fun v =>
    (V.posterior v, continuousPhi (V.posterior v))
  have hFmeas : Measurable F := by
    exact V.posterior_measurable_map.prodMk
      (continuous_continuousPhi.measurable.comp V.posterior_measurable_map)
  have hFmem (v : ι) : F v ∈
      (phiGraph : Set ((α × β → ℝ) × ℝ)) := by
    refine ⟨V.posterior v, V.posterior_isPMF v, ?_⟩
    dsimp [F]
    rw [Phi_eq_continuousPhi (V.posterior_isPMF v)]
  obtain ⟨C, hC⟩ :=
    (isCompact_phiGraph (α := α) (β := β)).isBounded.exists_norm_le
  have hFint : Integrable F V.prior := by
    apply Integrable.of_bound hFmeas.aestronglyMeasurable C
    exact ae_of_all _ fun v => hC (F v) (hFmem v)
  have hHull : (∫ v, F v ∂V.prior) ∈
      convexHull ℝ (phiGraph : Set ((α × β → ℝ) × ℝ)) := by
    exact (convex_convexHull ℝ (phiGraph : Set ((α × β → ℝ) × ℝ))).integral_mem
      (isCompact_convexHull_phiGraph hp).isClosed
      (ae_of_all _ fun v => subset_convexHull ℝ _ (hFmem v)) hFint
  have hpostInt : Integrable V.posterior V.prior := by
    simpa [F] using hFint.fst
  have hphiInt : Integrable (fun v => continuousPhi (V.posterior v)) V.prior := by
    simpa [F] using hFint.snd
  have hfirst : (∫ v, V.posterior v ∂V.prior) = p := by
    funext z
    calc
      (∫ v, V.posterior v ∂V.prior) z =
          ∫ v, V.posterior v z ∂V.prior := by
        exact ((ContinuousLinearMap.proj (R := ℝ) z).integral_comp_comm hpostInt).symm
      _ = p z := V.barycenter z
  have hsecond :
      (∫ v, continuousPhi (V.posterior v) ∂V.prior) = V.payoff := by
    unfold payoff
    apply integral_congr_ae
    exact ae_of_all _ fun v => (Phi_eq_continuousPhi (V.posterior_isPMF v)).symm
  have hIntegral : (∫ v, F v ∂V.prior) = (p, V.payoff) := by
    calc
      (∫ v, F v ∂V.prior) =
          ((∫ v, V.posterior v ∂V.prior),
            ∫ v, continuousPhi (V.posterior v) ∂V.prior) := by
        exact integral_pair hpostInt hphiInt
      _ = (p, V.payoff) := by rw [hfirst, hsecond]
  rw [hIntegral] at hHull
  obtain ⟨W, hWpayoff⟩ := exists_latent_of_mem_convexHull_phiGraph hp hHull
  refine ⟨W, ?_⟩
  rw [W.score_eq hp, hWpayoff, V.infoScore_eq_Psi_sub_payoff hp]

theorem infoScore_nonneg (hp : IsPMF p) (V : GeneralLatent p ι) :
    0 ≤ V.infoScore := by
  obtain ⟨W, hW⟩ := V.exists_finite_score_eq hp
  rw [← hW]
  exact W.score_nonneg

end GeneralLatent

namespace PosteriorLatent

variable {p : α × β → ℝ}
variable {ι : Type u} [MeasurableSpace ι]

/-- Namespace-compatible form of exact finite compression. -/
theorem exists_finite_score_eq (hp : IsPMF p)
    (V : PosteriorLatent p ι) :
    ∃ W : Latent p, W.score = V.infoScore :=
  GeneralLatent.exists_finite_score_eq hp V

end PosteriorLatent

end stoch_to_det
