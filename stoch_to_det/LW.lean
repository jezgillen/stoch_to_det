import stoch_to_det.ConstantBound1771
import stoch_to_det.JointLatent

/-!
# Generalized stoch_to_det and the LessWrong sum theorem

Exact finite compression lets the improved finite theorem apply both to the
posterior-mixture interface and, through regular conditional distributions,
to an ordinary joint probability law of `(V,X,Y)`. Deterministic attainment
is exported at function level, so the same code (depending only on `p`) works
for every latent in either presentation.
-/

universe u

namespace stoch_to_det

open MeasureTheory

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- The exact improved finite theorem applies to every measurable posterior
latent after lossless finite compression. -/
theorem T_le_Cdagger1771_mul_generalScore
    {p : α × β → ℝ} (hp : IsPMF p)
    {ι : Type u} [MeasurableSpace ι]
    (V : GeneralLatent p ι) :
    T p ≤ Cdagger1771 * V.infoScore := by
  obtain ⟨W, hW⟩ := V.exists_finite_score_eq hp
  calc
    T p ≤ Cdagger1771 * tau p := T_le_Cdagger1771 hp
    _ ≤ Cdagger1771 * W.score :=
      mul_le_mul_of_nonneg_left (tau_le_score W) Cdagger1771_pos.le
    _ = Cdagger1771 * V.infoScore := by rw [hW]

/-- Rounded form of generalized stoch_to_det for an individual posterior latent. -/
theorem T_le_1771_mul_generalScore
    {p : α × β → ℝ} (hp : IsPMF p)
    {ι : Type u} [MeasurableSpace ι]
    (V : GeneralLatent p ι) :
    T p ≤ (1771 : ℝ) * V.infoScore := by
  have hCdagger : Cdagger1771 < (1771 : ℝ) := by
    unfold Cdagger1771
    linarith [KD1771_lt_1770]
  calc
    T p ≤ Cdagger1771 * V.infoScore :=
      T_le_Cdagger1771_mul_generalScore hp V
    _ ≤ (1771 : ℝ) * V.infoScore :=
      mul_le_mul_of_nonneg_right (le_of_lt hCdagger)
        (V.infoScore_nonneg hp)

/-- Any code attaining `T p` satisfies the exact generalized inequality. -/
theorem optimal_code_le_general_Cdagger1771
    {p : α × β → ℝ} (hp : IsPMF p)
    {γ : Type} [Fintype γ] [DecidableEq γ]
    {Γ : α × β → γ}
    (hΓ : (Latent.ofFunction hp Γ).score = T p)
    {ι : Type u} [MeasurableSpace ι]
    (V : GeneralLatent p ι) :
    detScore p Γ ≤ Cdagger1771 * V.infoScore := by
  rw [← Latent.ofFunction_score_eq_detScore hp Γ, hΓ]
  exact T_le_Cdagger1771_mul_generalScore hp V

/-- Any code attaining `T p` satisfies the rounded generalized inequality. -/
theorem optimal_code_le_general_1771
    {p : α × β → ℝ} (hp : IsPMF p)
    {γ : Type} [Fintype γ] [DecidableEq γ]
    {Γ : α × β → γ}
    (hΓ : (Latent.ofFunction hp Γ).score = T p)
    {ι : Type u} [MeasurableSpace ι]
    (V : GeneralLatent p ι) :
    detScore p Γ ≤ (1771 : ℝ) * V.infoScore := by
  rw [← Latent.ofFunction_score_eq_detScore hp Γ, hΓ]
  exact T_le_1771_mul_generalScore hp V

/-- Generalized stoch_to_det with the exact symbolic constant.

For each finite law `p`, one finite deterministic code, depending only on
`p`, works simultaneously for every measurable latent represented by its
posterior family. -/
theorem generalized_stoch_to_det_Cdagger1771
    {p : α × β → ℝ} (hp : IsPMF p) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      condH Γ (fun z : α × β => z) p = 0 ∧
      ∀ {ι : Type u} [MeasurableSpace ι]
        (V : GeneralLatent p ι),
        detScore p Γ ≤ Cdagger1771 * V.infoScore := by
  obtain ⟨Γ, hΓ⟩ := exists_T_optimal_code hp
  refine ⟨Γ, condH_function_given_pair_zero hp Γ, ?_⟩
  intro ι _ V
  exact optimal_code_le_general_Cdagger1771 hp hΓ V

/-- Uniform rounded form of generalized stoch_to_det. The same deterministic code,
chosen solely from `p`, works for every measurable posterior latent. -/
theorem generalized_stoch_to_det_1771
    {p : α × β → ℝ} (hp : IsPMF p) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      condH Γ (fun z : α × β => z) p = 0 ∧
      ∀ {ι : Type u} [MeasurableSpace ι]
        (V : GeneralLatent p ι),
        detScore p Γ ≤ (1771 : ℝ) * V.infoScore := by
  obtain ⟨Γ, hΓdet, hΓ⟩ := generalized_stoch_to_det_Cdagger1771 hp
  refine ⟨Γ, hΓdet, ?_⟩
  intro ι _ V
  have hCdagger : Cdagger1771 < (1771 : ℝ) := by
    unfold Cdagger1771
    linarith [KD1771_lt_1770]
  exact (hΓ V).trans <| mul_le_mul_of_nonneg_right
    (le_of_lt hCdagger) (V.infoScore_nonneg hp)

/-- Strengthened LessWrong sum theorem, retaining exact determinism of the
finite witness. -/
theorem LW_sum_1771_strong
    {p : α × β → ℝ} (hp : IsPMF p)
    {ι : Type u} [MeasurableSpace ι]
    (V : GeneralLatent p ι) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      condH Γ (fun z : α × β => z) p = 0 ∧
      detScore p Γ ≤ (1771 : ℝ) * V.infoScore := by
  obtain ⟨Γ, hΓdet, hΓ⟩ := generalized_stoch_to_det_1771 hp
  exact ⟨Γ, hΓdet, hΓ V⟩

/-- Dropping the displayed determinism conjunct and unfolding the two scores
turns the strengthened rounded statement into the bare LW-sum statement. -/
theorem LW_sum_1771_of_strong
    {p : α × β → ℝ}
    {ι : Type u} [MeasurableSpace ι]
    (V : GeneralLatent p ι)
    (hstrong :
      ∃ Γ : α × β → Fin (Fintype.card (α × β)),
        condH Γ (fun z : α × β => z) p = 0 ∧
        detScore p Γ ≤ (1771 : ℝ) * V.infoScore) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      condMI (fun z : α × β => z.1) (fun z => z.2) Γ p
        + condH Γ (fun z : α × β => z.1) p
        + condH Γ (fun z : α × β => z.2) p
      ≤ (1771 : ℝ) *
        (V.IxyGiven + V.IvxGivenY + V.IvyGivenX) := by
  obtain ⟨Γ, _, hΓ⟩ := hstrong
  exact ⟨Γ, by simpa [detScore, GeneralLatent.infoScore] using hΓ⟩

/-- Modified LessWrong desideratum: the three deterministic information
terms are bounded by `1771` times the three general-latent information terms. -/
theorem LW_sum_1771
    {p : α × β → ℝ} (hp : IsPMF p)
    {ι : Type u} [MeasurableSpace ι]
    (V : GeneralLatent p ι) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      condMI (fun z : α × β => z.1) (fun z => z.2) Γ p
        + condH Γ (fun z : α × β => z.1) p
        + condH Γ (fun z : α × β => z.2) p
      ≤ (1771 : ℝ) *
        (V.IxyGiven + V.IvxGivenY + V.IvyGivenX) := by
  exact LW_sum_1771_of_strong V (LW_sum_1771_strong hp V)

/-! ### Ordinary joint-law latents -/

section JointLaw

variable [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- The exact improved theorem for a latent supplied as an ordinary joint
probability law of `(V,(X,Y))`. The posterior used by compression is obtained
canonically by disintegration. -/
theorem T_le_Cdagger1771_mul_jointScore
    {p : α × β → ℝ} (hp : IsPMF p)
    {ι : Type u} [MeasurableSpace ι]
    (V : JointLatent p ι) :
    T p ≤ Cdagger1771 * V.infoScore := by
  simpa using T_le_Cdagger1771_mul_generalScore hp (V.toGeneralLatent hp)

/-- Rounded generalized stoch_to_det for an ordinary joint-law latent. -/
theorem T_le_1771_mul_jointScore
    {p : α × β → ℝ} (hp : IsPMF p)
    {ι : Type u} [MeasurableSpace ι]
    (V : JointLatent p ι) :
    T p ≤ (1771 : ℝ) * V.infoScore := by
  simpa using T_le_1771_mul_generalScore hp (V.toGeneralLatent hp)

/-- Any deterministic code attaining `T p` satisfies the exact inequality
against an ordinary joint-law latent. -/
theorem optimal_code_le_joint_Cdagger1771
    {p : α × β → ℝ} (hp : IsPMF p)
    {γ : Type} [Fintype γ] [DecidableEq γ]
    {Γ : α × β → γ}
    (hΓ : (Latent.ofFunction hp Γ).score = T p)
    {ι : Type u} [MeasurableSpace ι]
    (V : JointLatent p ι) :
    detScore p Γ ≤ Cdagger1771 * V.infoScore := by
  simpa using optimal_code_le_general_Cdagger1771 hp hΓ
    (V.toGeneralLatent hp)

/-- Uniform rounded joint-law theorem. The witness is selected before both
the measurable latent alphabet and its joint probability law. -/
theorem generalized_stoch_to_det_1771_joint
    {p : α × β → ℝ} (hp : IsPMF p) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      condH Γ (fun z : α × β => z) p = 0 ∧
      ∀ {ι : Type u} [MeasurableSpace ι]
        (V : JointLatent p ι),
        detScore p Γ ≤ (1771 : ℝ) * V.infoScore := by
  obtain ⟨Γ, hΓdet, hΓ⟩ := generalized_stoch_to_det_Cdagger1771 hp
  refine ⟨Γ, hΓdet, ?_⟩
  intro ι _ V
  have hCdagger : Cdagger1771 < (1771 : ℝ) := by
    unfold Cdagger1771
    linarith [KD1771_lt_1770]
  have hΓV : detScore p Γ ≤ Cdagger1771 * V.infoScore := by
    simpa using hΓ (V.toGeneralLatent hp)
  exact hΓV.trans <| mul_le_mul_of_nonneg_right
    (le_of_lt hCdagger) (V.infoScore_nonneg hp)

/-- Rounded joint-law theorem, retaining the one `p`-dependent deterministic
witness. -/
theorem LW_sum_1771_joint_strong
    {p : α × β → ℝ} (hp : IsPMF p)
    {ι : Type u} [MeasurableSpace ι]
    (V : JointLatent p ι) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      condH Γ (fun z : α × β => z) p = 0 ∧
      detScore p Γ ≤ (1771 : ℝ) * V.infoScore := by
  obtain ⟨Γ, hΓdet, hΓ⟩ := generalized_stoch_to_det_1771_joint hp
  exact ⟨Γ, hΓdet, hΓ V⟩

/-- Explicit implication from the strengthened deterministic joint-law
statement to the displayed function-witness LW sum.  The genuinely bare
finite-latent corollary is `LW_sum_1771_joint` in `stoch_to_det.MainTheorems`. -/
theorem LW_sum_1771_joint_of_strong
    {p : α × β → ℝ}
    {ι : Type u} [MeasurableSpace ι]
    (V : JointLatent p ι)
    (hstrong :
      ∃ Γ : α × β → Fin (Fintype.card (α × β)),
        condH Γ (fun z : α × β => z) p = 0 ∧
        detScore p Γ ≤ (1771 : ℝ) * V.infoScore) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      condMI (fun z : α × β => z.1) (fun z => z.2) Γ p
        + condH Γ (fun z : α × β => z.1) p
        + condH Γ (fun z : α × β => z.2) p
      ≤ (1771 : ℝ) *
        (V.IxyGiven + V.IvxGivenY + V.IvyGivenX) := by
  obtain ⟨Γ, _, hΓ⟩ := hstrong
  exact ⟨Γ, by simpa [detScore, JointLatent.infoScore] using hΓ⟩

end JointLaw

end stoch_to_det
