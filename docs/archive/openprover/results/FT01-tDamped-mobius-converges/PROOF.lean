-- Summary: Complete assembled proof of tDamped_mobius_converges: T-damped Möbius iteration converges for 0<g<1.
import Mathlib

open Filter Topology

namespace Plan.FT01

def dampedMap (lam : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ := (1 - lam) * u + lam * g u

-- H is a self-map with T* = Ts as the unique positive fixed point; H is monotone on (0,∞);
-- points below Ts are pushed up (hup), points above Ts are pushed down (hdown); H is continuous
-- at every positive real. Then the orbit of ANY positive starting point T0 under H converges to Ts.
lemma orbit_tendsto_of_monotone {H : ℝ → ℝ} {Ts T0 : ℝ} (hTs : 0 < Ts) (hT0 : 0 < T0)
    (hmono : ∀ S T, 0 < S → S ≤ T → H S ≤ H T) (hfix : H Ts = Ts)
    (hup : ∀ T, 0 < T → T ≤ Ts → T ≤ H T) (hdown : ∀ T, Ts ≤ T → H T ≤ T)
    (hcont : ∀ T, 0 < T → ContinuousAt H T)
    (huniq : ∀ L, 0 < L → H L = L → L = Ts) :
    Tendsto (fun n => H^[n] T0) atTop (𝓝 Ts) := by
  cases le_total T0 Ts with
  | inl hle =>
    have hbounds : ∀ n, T0 ≤ H^[n] T0 ∧ H^[n] T0 ≤ Ts := by
      intro n
      induction n with
      | zero => exact ⟨le_rfl, hle⟩
      | succ n ih =>
        have h1 : T0 ≤ H^[n] T0 := ih.1
        have h2 : H^[n] T0 ≤ Ts := ih.2
        have hposn : 0 < H^[n] T0 := lt_of_lt_of_le hT0 h1
        rw [Function.iterate_succ_apply' H n T0]
        exact ⟨le_trans h1 (hup (H^[n] T0) hposn h2),
          le_trans (hmono (H^[n] T0) Ts hposn h2) (le_of_eq hfix)⟩
    have hmono_seq : Monotone (fun n : ℕ => H^[n] T0) :=
      monotone_nat_of_le_succ fun n => by
        rw [Function.iterate_succ_apply' H n T0]
        exact hup (H^[n] T0) (lt_of_lt_of_le hT0 (hbounds n).1) (hbounds n).2
    have hbdd : BddAbove (Set.range (fun n : ℕ => H^[n] T0)) :=
      ⟨Ts, fun x hx => by
        obtain ⟨k, rfl⟩ := hx
        exact (hbounds k).2⟩
    set L := ⨆ i : ℕ, H^[i] T0
    have htend : Tendsto (fun n : ℕ => H^[n] T0) atTop (𝓝 L) :=
      tendsto_atTop_ciSup hmono_seq hbdd
    have hLpos : 0 < L := lt_of_lt_of_le hT0 (ge_of_tendsto' htend (fun n => (hbounds n).1))
    have hcontL : ContinuousAt H L := hcont L hLpos
    have hfixL : H L = L := isFixedPt_of_tendsto_iterate htend hcontL
    rw [huniq L hLpos hfixL] at htend
    exact htend
  | inr hle =>
    have hbounds : ∀ n, Ts ≤ H^[n] T0 ∧ H^[n] T0 ≤ T0 := by
      intro n
      induction n with
      | zero => exact ⟨hle, le_rfl⟩
      | succ n ih =>
        have h1 : Ts ≤ H^[n] T0 := ih.1
        have h2 : H^[n] T0 ≤ T0 := ih.2
        rw [Function.iterate_succ_apply' H n T0]
        exact ⟨(le_of_eq hfix.symm).trans (hmono Ts (H^[n] T0) hTs h1),
          le_trans (hdown (H^[n] T0) h1) h2⟩
    have hanti : Antitone (fun n : ℕ => H^[n] T0) :=
      antitone_nat_of_succ_le fun n => by
        rw [Function.iterate_succ_apply' H n T0]
        exact hdown (H^[n] T0) (hbounds n).1
    have hbdd : BddBelow (Set.range (fun n : ℕ => H^[n] T0)) :=
      ⟨Ts, fun x hx => by
        obtain ⟨k, rfl⟩ := hx
        exact (hbounds k).1⟩
    set L := ⨅ i : ℕ, H^[i] T0
    have htend : Tendsto (fun n : ℕ => H^[n] T0) atTop (𝓝 L) :=
      tendsto_atTop_ciInf hanti hbdd
    have hLpos : 0 < L := lt_of_lt_of_le hTs (ge_of_tendsto' htend (fun n => (hbounds n).1))
    have hcontL : ContinuousAt H L := hcont L hLpos
    have hfixL : H L = L := isFixedPt_of_tendsto_iterate htend hcontL
    rw [huniq L hLpos hfixL] at htend
    exact htend

-- Ts = (1-g)/c is positive since g < 1 and c > 0.
lemma hTs_pos {g c : ℝ} (hg1 : g < 1) (hc : 0 < c) : 0 < (1 - g) / c := by
  positivity

-- Ts = (1-g)/c is a fixed point of H, since g + c*Ts = 1.
lemma hfix {g c lam : ℝ} (_hg0 : 0 < g) (_hg1 : g < 1) (hc : 0 < c) :
    dampedMap lam (fun T => T / (g + c * T)) ((1 - g) / c) = (1 - g) / c := by
  simp only [dampedMap]
  have hden : g + c * ((1 - g) / c) = 1 := by
    field_simp [hc.ne']
    ring
  rw [hden]
  field_simp
  ring

lemma hup {g c lam : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (hc : 0 < c) (hl0 : 0 < lam) :
    ∀ T : ℝ, 0 < T → T ≤ (1 - g) / c → T ≤ dampedMap lam (fun T => T / (g + c * T)) T := by
  intro T hT0 hTle
  simp only [dampedMap]
  have hpos : 0 < g + c * T := by nlinarith
  have hTc : T * c ≤ 1 - g := (le_div_iff₀ hc).mp hTle
  have hphi : T ≤ T / (g + c * T) := by
    rw [le_div_iff₀ hpos]
    nlinarith [hTc]
  nlinarith [hphi, hg0, hg1, hc, hl0, hT0]

lemma hdown {g c lam : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (hc : 0 < c) (hl0 : 0 < lam) :
    ∀ T : ℝ, (1 - g) / c ≤ T → dampedMap lam (fun T => T / (g + c * T)) T ≤ T := by
  intro T hTle
  simp only [dampedMap]
  have hT0 : 0 < T := lt_of_lt_of_le (div_pos (sub_pos.mpr hg1) hc) hTle
  have hpos : 0 < g + c * T := by nlinarith
  have hTc : 1 - g ≤ T * c := (div_le_iff₀ hc).mp hTle
  have hphi : T / (g + c * T) ≤ T := by
    rw [div_le_iff₀ hpos]
    nlinarith [hTc]
  nlinarith [hphi, hg0, hg1, hc, hl0, hT0]

lemma huniq {g c lam : ℝ} (hg0 : 0 < g) (hc : 0 < c) (hl0 : 0 < lam) :
    ∀ L : ℝ, 0 < L → dampedMap lam (fun T => T / (g + c * T)) L = L → L = (1 - g) / c := by
  intro L hL0 heq
  simp only [dampedMap] at heq
  have hpos : 0 < g + c * L := by nlinarith
  have h1 : lam * (L / (g + c * L)) = lam * L := by nlinarith
  have h2 : L / (g + c * L) = L := by
    apply mul_left_cancel₀ (ne_of_gt hl0)
    exact h1
  have h3 : L = L * (g + c * L) := by
    rw [div_eq_iff (ne_of_gt hpos)] at h2
    exact h2
  have h4 : 1 = g + c * L := by
    rw [← mul_left_inj' (ne_of_gt hL0)]
    nlinarith [h3]
  have h5 : c * L = 1 - g := by nlinarith [h4]
  rw [eq_comm, div_eq_iff hc.ne']
  nlinarith [h5]

lemma hmono {g c lam : ℝ} (hg0 : 0 < g) (hc : 0 < c) (hl0 : 0 < lam) (hl1 : lam ≤ 1) :
    ∀ S T : ℝ, 0 < S → S ≤ T →
      dampedMap lam (fun T => T / (g + c * T)) S ≤ dampedMap lam (fun T => T / (g + c * T)) T := by
  intro S T hS hST
  have hSg : 0 < g + c * S := by nlinarith
  have hSTg : 0 < g + c * T := by nlinarith
  have hphi : S / (g + c * S) ≤ T / (g + c * T) := by
    rw [div_le_div_iff₀ hSg hSTg]
    nlinarith
  have h1 : (1 - lam) * S ≤ (1 - lam) * T := by
    exact mul_le_mul_of_nonneg_left hST (by linarith : 0 ≤ 1 - lam)
  have h2 : lam * (S / (g + c * S)) ≤ lam * (T / (g + c * T)) := by
    exact mul_le_mul_of_nonneg_left hphi hl0.le
  simp only [dampedMap]
  nlinarith

lemma hcont {g c lam : ℝ} (hg0 : 0 < g) (hc : 0 < c) :
    ∀ T : ℝ, 0 < T → ContinuousAt (dampedMap lam (fun T => T / (g + c * T))) T := by
  intro T hT
  unfold dampedMap
  have hden : g + c * T ≠ 0 := by
    have : 0 < g + c * T := by nlinarith
    exact ne_of_gt this
  apply ContinuousAt.add
  · exact continuousAt_const.mul continuousAt_id
  · apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.div continuousAt_id
      (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
      hden

theorem tDamped_mobius_converges {g c lam : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (hc : 0 < c)
    (hl0 : 0 < lam) (hl1 : lam ≤ 1) (T0 : ℝ) (hT0 : 0 < T0) :
    Tendsto (fun n => (dampedMap lam (fun T => T / (g + c * T)))^[n] T0) atTop
      (𝓝 ((1 - g) / c)) := by
  exact orbit_tendsto_of_monotone (H := dampedMap lam (fun T => T / (g + c * T)))
    (Ts := (1 - g) / c)
    (hTs_pos hg1 hc) hT0
    (hmono hg0 hc hl0 hl1)
    (hfix hg0 hg1 hc)
    (hup hg0 hg1 hc hl0)
    (hdown hg0 hg1 hc hl0)
    (hcont hg0 hc)
    (huniq hg0 hc hl0)

end Plan.FT01
