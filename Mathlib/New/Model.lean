import Mathlib.Data.Part
import Mathlib.New.Comp

set_option linter.style.lambdaSyntax false
set_option autoImplicit false

class LinearMonad m [Monad m] where
  mem {α} : α → m α → Prop := λ a x ↦ x = pure a
  bind' {α β} (k : m α) (f : (x : α) → (mem x k) → m β) : m β

class ExistingMonad m [Monad m] where
  ex {α} (k : m α) : ∃ x, k = pure x

-- also, `Delayed α → IO α`


instance : LinearMonad Squash where
  bind' k := k.recOnSubsingleton λ x f ↦ f x rfl

instance : LinearMonad Option where
  bind' k := k.rec (λ _ ↦ none) (λ x f ↦ f x rfl)

instance : LinearMonad PComp where
  mem a x := ∃ n, x.iterate n = a
  bind' := @λ α β x _f ↦
    let ⟨f, hf⟩ :
      {f : ∀ n a, x.iterate n = some a → PComp β // ∀ n m a h₁ h₂, f n a h₁ = f m a h₂} :=
        ⟨λ n a h ↦ _f a ⟨n, h⟩, λ _ _ _ _ _ ↦ rfl⟩
    { iterate n :=
        f n |> (x.iterate n).rec
          (λ _ ↦ none)
          (λ a f ↦ (f a rfl).iterate n)
      prop := by
        rcases x with ⟨x, hx⟩
        dsimp
        dsimp at f
        dsimp at hf
        intros m n b hle heq
        specialize hf n m
        generalize f n = fn at *
        generalize f m = fm at *
        have := λ r ↦ @hx m n r hle
        generalize x n = xn at *
        generalize x m = xm at *
        cases xm with
        | none =>
            {
              simp at heq
            }
        | some xm =>
            {
              simp at heq
              have := this xm rfl
              subst this
              simp only
              rw [hf xm rfl rfl]
              exact (fm xm rfl).prop hle heq
            }
    }

instance : LinearMonad Part where
  bind' k f :=
    ⟨∃ h : k.Dom, (f (k.get h) (Part.ext' ⟨λ _ ↦ True.intro, λ _ ↦ h⟩ (λ _ _ ↦ by simp))).Dom,
      λ h ↦ (f (k.get h.1) _).get h.2⟩


instance : ExistingMonad Squash where
  ex k := k.recOnSubsingleton λ x ↦ ⟨x, rfl⟩
