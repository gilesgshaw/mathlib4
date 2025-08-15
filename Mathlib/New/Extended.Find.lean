import Mathlib.New.Extended
import Mathlib.Data.Nat.Find

namespace Extended
  variable {p : Nat → Prop} {dec : DecidablePred p} {n : Nat}

def find (p : Nat → Prop) [DecidablePred p] : Nat† := ⟨_, Nat.find (p:=p)⟩

@[simp, iff_back]
theorem find_isFinite_iff : (find p).IsFinite ↔ ∃ n, p n :=
  by simp [find]

@[simp, iff_back mem_find_of_least]
theorem mem_find_iff : n ∈ find p ↔ p n ∧ ∀ m < n, ¬p m :=
  by simpa [find, Nat.find_eq_iff] using by intros; constructor; assumption

@[simp, iff_back find_eq_of_least]
theorem find_eq_iff : find p = ↑n ↔ p n ∧ ∀ m < n, ¬p m :=
  mem_find_iff

@[simp, iff_back eq_find_of_least]
theorem eq_find_iff : ↑n = find p ↔ p n ∧ ∀ m < n, ¬p m :=
  eq_comm.trans mem_find_iff

theorem find_spec_of_mem (h : n ∈ find p) : p n :=
  mem_find_iff.mp h |>.1

theorem find_spec_of_eq (h : find p = ↑n) : p n :=
  find_spec_of_mem h

theorem find_spec_get {h} : p ((find p).get h) :=
  find_spec_of_mem get_mem

theorem find_le (h : p n) : find p ≤ ↑n :=
  get_le_iff (h:=find_isFinite ⟨_, h⟩) |>.mp (Nat.find_le h)

theorem not_of_lt_find (h : ↑n < find p) : ¬p n :=
  λ hc ↦ find_le hc |>.not_gt h

@[simp] theorem find_lt_iff : find p < n ↔ ∃ m < n, p m :=
  .intro
    (λ h ↦ (lt_finite_iff.mp h).imp λ _ ⟨h₁, h₂⟩ ↦ ⟨h₂, find_spec_of_mem h₁⟩)
    (λ ⟨_, h₁, h₂⟩ ↦ (find_le h₂).trans_lt (finite_lt_finite h₁))

@[simp] theorem find_le_iff : find p ≤ n ↔ ∃ m ≤ n, p m :=
  .intro
    (λ h ↦ (le_finite_iff.mp h).imp λ _ ⟨h₁, h₂⟩ ↦ ⟨h₂, find_spec_of_mem h₁⟩)
    (λ ⟨_, h₁, h₂⟩ ↦ (find_le h₂).trans (finite_le_finite h₁))

@[simp] theorem lt_find_iff : n < find p ↔ ∀ m ≤ n, ¬p m :=
  .intro
    (λ h _ hm hc ↦ (find_le hc).trans (finite_le_finite hm) |>.not_gt h)
    (λ h ↦ (finite_lt_iff).mpr λ m hm ↦ lt_of_not_ge λ hc ↦ h m hc (find_spec_of_mem hm))

@[simp] theorem le_find_iff : n ≤ find p ↔ ∀ m < n, ¬p m :=
  .intro
    (λ h _ hm hc ↦ (find_le hc).trans_lt (finite_lt_finite hm) |>.not_ge h)
    (λ h ↦ (finite_le_iff).mpr λ m hm ↦ le_of_not_gt λ hc ↦ h m hc (find_spec_of_mem hm))

@[simp high] theorem find_le_iff' (h : Monotone p) : find p ≤ n ↔ p n :=
  find_le_iff.trans ⟨Exists.rec λ _ ⟨h₁, h₂⟩ ↦ h h₁ h₂, λ h ↦ ⟨n, le_rfl, h⟩⟩

@[simp high] theorem lt_find_iff' (h : Monotone p) : n < find p ↔ ¬p n :=
  lt_find_iff.trans ⟨λ h ↦ h n le_rfl, λ h₁ _ h₂ ↦ h₁ ∘ h h₂⟩

end Extended
