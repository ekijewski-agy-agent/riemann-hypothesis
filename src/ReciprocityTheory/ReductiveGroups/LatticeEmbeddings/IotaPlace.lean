module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
import Formalism.SharedLemmas.NormLeOneOfIntegral
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain

namespace ReciprocityTheory.ChartRestriction.B3.IotaPl

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

theorem norm_int_le (ι : K →+* ℂ_[p]) (y : 𝓞 K) : ‖ι (y : K)‖ ≤ 1 := by
  obtain ⟨f, hf, hfy⟩ := NumberField.RingOfIntegers.isIntegral_coe y
  refine Formalism.SharedLemmas.norm_le_one_of_isIntegral ⟨f, hf, ?_⟩
  convert congrArg ι hfy using 1
  · rw [Polynomial.hom_eval₂]
    exact congrArg (fun φ => Polynomial.eval₂ φ (ι (y : K)) f) (RingHom.ext_int _ _)
  · exact (map_zero ι).symm

def smallIdeal (ι : K →+* ℂ_[p]) : Ideal (𝓞 K) where
  carrier := {y | ‖ι (y : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : ι ((a + b : 𝓞 K) : K) = ι (a : K) + ι (b : K) := by simp
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : ι ((c • a : 𝓞 K) : K) = ι (c : K) * ι (a : K) := by simp
    rw [this, norm_mul]
    have h1 := norm_int_le ι c
    nlinarith [norm_nonneg (ι (c : K)), norm_nonneg (ι (a : K))]

theorem mem_smallIdeal (ι : K →+* ℂ_[p]) (y : 𝓞 K) : y ∈ smallIdeal ι ↔ ‖ι (y : K)‖ < 1 := Iff.rfl

theorem smallIdeal_isPrime (ι : K →+* ℂ_[p]) : (smallIdeal ι).IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : 𝓞 K) ∈ smallIdeal ι := (Ideal.eq_top_iff_one _).mp h
    rw [mem_smallIdeal] at h1
    simp at h1
  · intro a b hab
    simp only [mem_smallIdeal] at hab ⊢
    have e : ι ((a * b : 𝓞 K) : K) = ι (a : K) * ι (b : K) := by simp
    rw [e, norm_mul] at hab
    by_contra hc
    push_neg at hc
    obtain ⟨ha, hb⟩ := hc
    nlinarith [norm_int_le ι a, norm_int_le ι b]

end ReciprocityTheory.ChartRestriction.B3.IotaPl

namespace ReciprocityTheory.ChartRestriction.B3

end ReciprocityTheory.ChartRestriction.B3
