import stoch_to_det.GeneralLatent
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Measurable latents presented by a joint probability law

`stoch_to_det.GeneralLatent` is the posterior-mixture interface used by the exact
finite-compression argument.  This module supplies the missing user-facing
bridge from an ordinary probability law of `(V, X, Y)`.

Because `(X,Y)` is finite and discrete, its regular conditional distribution
given `V` exists.  Evaluating that kernel on singletons gives a measurable
family of finite posterior PMFs.  The disintegration identity proves the
barycenter equation, so no posterior data is assumed from the caller.
-/

universe u

namespace stoch_to_det

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-! ### Finite PMFs as ordinary measures -/

/-- The discrete measure associated to a real-valued finite PMF.  The
`ENNReal.ofReal` is harmless under an `IsPMF` hypothesis. -/
noncomputable def pmfMeasure {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    (p : Ω → ℝ) : Measure Ω :=
  Measure.sum fun z => ENNReal.ofReal (p z) • Measure.dirac z

theorem pmfMeasure_real_singleton {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {p : Ω → ℝ} (hp : IsPMF p) (z : Ω) :
    (pmfMeasure p).real {z} = p z := by
  change ((Measure.sum fun x =>
    ENNReal.ofReal (p x) • Measure.dirac x) {z}).toReal = p z
  rw [Measure.sum_smul_dirac_singleton]
  simp [hp.nonneg z]

theorem isProbabilityMeasure_pmfMeasure {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] {p : Ω → ℝ} (hp : IsPMF p) :
    IsProbabilityMeasure (pmfMeasure p) := by
  apply HasSum.isProbabilityMeasure_sum_dirac hp.nonneg
  have hsum : ∑ z, p z = 1 := by simpa [mass] using hp.total
  simpa [hsum] using (hasSum_fintype p)

/-! ### Joint-law latents and their regular conditional law -/

/-- An ordinary joint probability law of `(V,(X,Y))` whose `(X,Y)` marginal
is the finite PMF `p`.

Unlike `GeneralLatent`, this structure asks the caller for no conditional
probabilities. -/
structure JointLatent (p : α × β → ℝ) (ι : Type u)
    [MeasurableSpace ι] [MeasurableSpace α] [MeasurableSpace β] where
  law : Measure (ι × (α × β))
  law_isProbability : IsProbabilityMeasure law
  xy_marginal : law.map Prod.snd = pmfMeasure p

namespace JointLatent

variable {p : α × β → ℝ}
variable {ι : Type u} [MeasurableSpace ι]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- The marginal law of the latent variable. -/
noncomputable def prior (V : JointLatent p ι) : Measure ι :=
  V.law.map Prod.fst

/-- The regular conditional law of `(X,Y)` given the latent variable. -/
noncomputable def conditionalKernel (V : JointLatent p ι) :
    Kernel ι (α × β) := by
  letI : IsProbabilityMeasure V.law := V.law_isProbability
  letI : Nonempty (α × β) :=
    (nonempty_of_isProbabilityMeasure V.law).map Prod.snd
  exact condDistrib Prod.snd Prod.fst V.law

instance conditionalKernel_isMarkov (V : JointLatent p ι) :
    IsMarkovKernel V.conditionalKernel := by
  unfold conditionalKernel
  infer_instance

/-- The joint law is reconstructed exactly from its latent marginal and its
regular conditional distribution. -/
theorem prior_compProd_conditionalKernel (V : JointLatent p ι) :
    V.prior ⊗ₘ V.conditionalKernel = V.law := by
  letI : IsProbabilityMeasure V.law := V.law_isProbability
  letI : Nonempty (α × β) :=
    (nonempty_of_isProbabilityMeasure V.law).map Prod.snd
  simpa [prior, conditionalKernel] using
    (compProd_map_condDistrib (μ := V.law) (X := Prod.fst)
      (Y := Prod.snd) measurable_snd.aemeasurable)

/-- The supplied finite marginal really has point masses `p z`. -/
theorem xy_marginal_real_singleton (hp : IsPMF p)
    (V : JointLatent p ι) (z : α × β) :
    (V.law.map Prod.snd).real {z} = p z := by
  rw [V.xy_marginal]
  exact pmfMeasure_real_singleton hp z

/-- The singleton probabilities of the regular conditional law. -/
noncomputable def posterior (V : JointLatent p ι)
    (v : ι) (z : α × β) : ℝ :=
  (V.conditionalKernel v).real {z}

theorem posterior_measurable (V : JointLatent p ι) (z : α × β) :
    Measurable (fun v => V.posterior v z) := by
  exact (V.conditionalKernel.measurable_coe
    (MeasurableSet.singleton z)).ennreal_toReal

theorem posterior_isPMF (V : JointLatent p ι) (v : ι) :
    IsPMF (V.posterior v) := by
  letI : IsProbabilityMeasure (V.conditionalKernel v) :=
    IsMarkovKernel.isProbabilityMeasure v
  constructor
  · intro z
    exact ENNReal.toReal_nonneg
  · unfold mass posterior
    rw [sum_measureReal_singleton]
    simp

theorem prior_isProbability (V : JointLatent p ι) :
    IsProbabilityMeasure V.prior := by
  letI : IsProbabilityMeasure V.law := V.law_isProbability
  exact V.law.isProbabilityMeasure_map measurable_fst.aemeasurable

/-- Integrating the conditional point masses recovers the `(X,Y)` marginal.
This is the coordinate form of disintegration used by `GeneralLatent`. -/
theorem integral_posterior (hp : IsPMF p) (V : JointLatent p ι)
    (z : α × β) :
    ∫ v, V.posterior v z ∂V.prior = p z := by
  letI : IsProbabilityMeasure V.law := V.law_isProbability
  letI : Nonempty (α × β) :=
    (nonempty_of_isProbabilityMeasure V.law).map Prod.snd
  have hfinite : ∀ v : ι, V.conditionalKernel v {z} < ∞ := fun v =>
    (measure_mono (Set.subset_univ {z})).trans_lt (by simp)
  calc
    ∫ v, V.posterior v z ∂V.prior =
        (∫⁻ v, V.conditionalKernel v {z} ∂V.prior).toReal := by
      exact integral_toReal
        (V.conditionalKernel.measurable_coe
          (MeasurableSet.singleton z)).aemeasurable
        (ae_of_all _ hfinite)
    _ = (V.conditionalKernel ∘ₘ V.prior).real {z} := by
      change (∫⁻ v, V.conditionalKernel v {z} ∂V.prior).toReal =
        ((V.conditionalKernel ∘ₘ V.prior) {z}).toReal
      rw [Measure.bind_apply (MeasurableSet.singleton z)
        V.conditionalKernel.aemeasurable]
    _ = (V.law.map Prod.snd).real {z} := by
      rw [prior, conditionalKernel]
      rw [condDistrib_comp_map measurable_fst.aemeasurable
        measurable_snd.aemeasurable]
    _ = p z := V.xy_marginal_real_singleton hp z

/-- Construct the posterior-mixture interface canonically from an ordinary
joint law.  This is exact disintegration, not an additional assumption. -/
noncomputable def toGeneralLatent (hp : IsPMF p)
    (V : JointLatent p ι) : GeneralLatent p ι where
  prior := V.prior
  prior_isProbability := V.prior_isProbability
  posterior := V.posterior
  posterior_measurable := V.posterior_measurable
  posterior_isPMF := V.posterior_isPMF
  barycenter := V.integral_posterior hp

/-! ### Conventional finite-output conditional information -/

/-- `I(X;Y | V)` for the original joint law, expressed through its regular
conditional law of the finite pair `(X,Y)`. -/
noncomputable def IxyGiven (V : JointLatent p ι) : ℝ :=
  ∫ v, Ixy (V.posterior v) ∂V.prior

/-- `I(V;X | Y) = H(X|Y) - H(X|V,Y)` for the original joint law.
The second conditional entropy is evaluated by first disintegrating over
`V`; all remaining alphabets are finite. -/
noncomputable def IvxGivenY (V : JointLatent p ι) : ℝ :=
  condH (fun z : α × β => z.1) (fun z => z.2) p -
    ∫ v, condH (fun z : α × β => z.1) (fun z => z.2)
      (V.posterior v) ∂V.prior

/-- `I(V;Y | X) = H(Y|X) - H(Y|V,X)` for the original joint law. -/
noncomputable def IvyGivenX (V : JointLatent p ι) : ℝ :=
  condH (fun z : α × β => z.2) (fun z => z.1) p -
    ∫ v, condH (fun z : α × β => z.2) (fun z => z.1)
      (V.posterior v) ∂V.prior

/-- The three conventional conditional-information terms of a joint-law
latent. -/
noncomputable def infoScore (V : JointLatent p ι) : ℝ :=
  V.IxyGiven + V.IvxGivenY + V.IvyGivenX

theorem infoScore_eq_info_sum (V : JointLatent p ι) :
    V.infoScore = V.IxyGiven + V.IvxGivenY + V.IvyGivenX := rfl

@[simp] theorem toGeneralLatent_IxyGiven (hp : IsPMF p)
    (V : JointLatent p ι) :
    (V.toGeneralLatent hp).IxyGiven = V.IxyGiven := rfl

@[simp] theorem toGeneralLatent_IvxGivenY (hp : IsPMF p)
    (V : JointLatent p ι) :
    (V.toGeneralLatent hp).IvxGivenY = V.IvxGivenY := rfl

@[simp] theorem toGeneralLatent_IvyGivenX (hp : IsPMF p)
    (V : JointLatent p ι) :
    (V.toGeneralLatent hp).IvyGivenX = V.IvyGivenX := rfl

@[simp] theorem toGeneralLatent_infoScore (hp : IsPMF p)
    (V : JointLatent p ι) :
    (V.toGeneralLatent hp).infoScore = V.infoScore := rfl

theorem infoScore_nonneg (hp : IsPMF p) (V : JointLatent p ι) :
    0 ≤ V.infoScore := by
  rw [← V.toGeneralLatent_infoScore hp]
  exact (V.toGeneralLatent hp).infoScore_nonneg hp

/-- Exact finite compression, now starting from an ordinary joint law. -/
theorem exists_finite_score_eq (hp : IsPMF p) (V : JointLatent p ι) :
    ∃ W : Latent p, W.score = V.infoScore := by
  simpa using (V.toGeneralLatent hp).exists_finite_score_eq hp

end JointLatent

end stoch_to_det
