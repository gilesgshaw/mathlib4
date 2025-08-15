import Mathlib.Data.Part
import Mathlib.Data.Nat.Find
import Mathlib.Data.Quot
set_option autoImplicit false
set_option linter.style.lambdaSyntax false
set_option linter.style.setOption false
set_option pp.beta true
set_option linter.style.dollarSyntax false



namespace Squash

instance : Monad Squash where
  pure := .mk
  bind := .lift

instance : LawfulMonad Squash := .mk' _
  (id_map     := λ _     ↦ Subsingleton.elim _ _)
  (pure_bind  := λ _ _   ↦ Subsingleton.elim _ _)
  (bind_assoc := λ _ _ _ ↦ Subsingleton.elim _ _)

end Squash



structure PComp α where
  iterate (n : Nat) : Option α
  prop {m n x} (hle : m ≤ n) (heq : iterate m = some x) : iterate n = some x

namespace PComp

variable {α β : Type _} {x y : PComp α} (self : PComp α)

@[ext] protected theorem ext (h : ∀ n, x.iterate n = y.iterate n) : x = y :=
  match x, y, funext h with | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

protected def pure (x : α) : PComp α where
  iterate _ := x
  prop _ h  := h

def map (f : α → β) (x : PComp α) : PComp β where
  iterate n  := (x.iterate n).map f
  prop hle heq :=
    Option.map_eq_some_iff.mp heq |>.elim λ _ ⟨h₁, h₂⟩ ↦
      x.prop hle h₁ ▸ congrArg some h₂

protected def bind (x : PComp α) (f : α → PComp β) : PComp β where
  iterate n  := (x.iterate n).bind λ x ↦ (f x).iterate n
  prop hle heq :=
    Option.bind_eq_some_iff.mp heq |>.elim λ a ⟨h₁, h₂⟩ ↦
      x.prop hle h₁ ▸ (f a).prop hle h₂

instance : Monad PComp where
  pure := .pure
  map  := .map
  bind := .bind

theorem pure_def (x : α) : Pure.pure x = PComp.pure x := rfl
theorem map_def (x : PComp α) (f : α → β) : Functor.map f x = PComp.map f x := rfl
theorem bind_def (x : PComp α) (f : α → PComp β) : Bind.bind x f = PComp.bind x f := rfl

instance : LawfulMonad PComp := .mk'
  (pure_bind      := λ _ _   ↦ rfl)
  (id_map         := λ _     ↦ PComp.ext λ _ ↦ Option.map_id')
  (bind_pure_comp := λ _ _   ↦ PComp.ext λ _ ↦ Option.map_eq_bind.symm)
  (bind_assoc     := λ _ _ _ ↦ PComp.ext λ _ ↦ Option.ext λ _ ↦
    by simpa [bind_def, PComp.bind, Option.bind_eq_some_iff] using
      ⟨λ ⟨b, ⟨a, h₁, h₂⟩, h₃⟩ ↦ ⟨a, h₁, b, h₂, h₃⟩,
        λ ⟨a, h₁, b, h₂, h₃⟩ ↦ ⟨b, ⟨a, h₁, h₂⟩, h₃⟩⟩)


def Dom : Prop := ∃ n, (self.iterate n).isSome

def get (h : self.Dom) : α := (self.iterate (Nat.find h)).get (Nat.find_spec h)

def toPart : Part α := ⟨self.Dom, self.get⟩

instance setoid : Setoid (PComp α) where
  r x y := ∀ a, (∃ n, x.iterate n = some a) ↔ (∃ n, y.iterate n = some a)
  iseqv := ⟨λ _ _ ↦ .rfl, λ h a ↦ (h a).symm, λ h₁ h₂ a ↦ (h₁ a).trans (h₂ a)⟩

end PComp



def Comp (α) := Quotient (@PComp.setoid α)

namespace Comp

variable {α β : Type _} {x y : Comp α} (self : Comp α)

def mk
    (iterate : (n : Nat) → Option α)
    (prop : ∀ {m n x}, (hle : m ≤ n) → (heq : iterate m = some x) → iterate n = some x) : Comp α :=
  Quotient.mk _ <| .mk iterate prop

-- def toPart : Part α := self.lift PComp.toPart (λ _ _ h ↦ h)

-- theorem toPart_inj : (@toPart α).Injective :=
--   Quotient.ind₂ λ _ _ h ↦ Quotient.sound h

-- @[ext] protected theorem ext (h : ∀ n, x.iterate n = y.iterate n) : x = y :=
--   match x, y, funext h with | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

-- @[ext] protected theorem ext (h : ∀ n, x.iterate n = y.iterate n) : x = y :=
--   match x, y, funext h with | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

protected def pure (x : α) : Comp α := ⟦.pure x⟧

def map (f : α → β) : (x : Comp α) → Comp β :=
  .lift (⟦·.map f⟧)
    (λ x y (h : ∀ _, _) ↦ Quot.sound λ _ ↦
      by simp_rw (singlePass := true)
        [PComp.map, Option.map_eq_some_iff, exists_comm, exists_and_right, h])

end Comp

#exit

namespace Comp

variable {α β : Type}

def squash (x : Comp (Comp α)) : Comp α :=
  sorry |> x.lift λ ⟨k, hk⟩ ↦
    have : Nat → Comp α := λ n ↦
      (k n).getD ⟦⟨λ _ ↦ none, λ _ h ↦ h⟩⟧
    _

protected def bind' (x : PComp α) (f : (a : α) → (∃ n, x.iterate n = some a) → Comp β) : Comp β := by
  rcases x with ⟨k, hk⟩
  dsimp at f
  _

  --x.lift (λ x ↦ have : (α → PComp β) → Comp _ := λ f ↦ ⟦x.bind f⟧; _) _

instance : Monad Comp where
  pure := .pure
  map  := .map
  bind := .bind

theorem pure_def (x : α) : Pure.pure x = Comp.pure x := rfl
theorem map_def (x : Comp α) (f : α → β) : Functor.map f x = Comp.map f x := rfl
theorem bind_def (x : Comp α) (f : α → Comp β) : Bind.bind x f = Comp.bind x f := rfl

instance : LawfulMonad Comp := .mk'
  (pure_bind      := λ _ _   ↦ rfl)
  (id_map         := λ _     ↦ Comp.ext λ _ ↦ Option.map_id')
  (bind_pure_comp := λ _ _   ↦ Comp.ext λ _ ↦ Option.map_eq_bind.symm)
  (bind_assoc     := λ _ _ _ ↦ Comp.ext λ _ ↦ Option.ext λ _ ↦
    by simpa [bind_def, Comp.bind, Option.bind_eq_some_iff] using
      ⟨λ ⟨b, ⟨a, h₁, h₂⟩, h₃⟩ ↦ ⟨a, h₁, b, h₂, h₃⟩,
        λ ⟨a, h₁, b, h₂, h₃⟩ ↦ ⟨b, ⟨a, h₁, h₂⟩, h₃⟩⟩)


instance setoid : Setoid (Comp α) where
  r     := InvImage Eq toPart
  iseqv := ⟨λ _ ↦ rfl, Eq.symm, Eq.trans⟩

end Comp
