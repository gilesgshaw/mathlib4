import Mathlib.Tactic.ToAdditive.Frontend
import Mathlib.Tactic.SimpRw
import Mathlib.Order.Monotone.Defs
import Mathlib.New.IffToImp

theorem And.forall {p q} {f : p ∧ q → Prop} : (∀ h, f h) ↔ (∀ hp hq, f ⟨hp, hq⟩) :=
  ⟨λ h hp hq ↦ h ⟨hp, hq⟩, λ h ⟨hp, hq⟩ ↦ h hp hq⟩

-- theorem heq_iff_types_eq_cast_eq (x : α) (y : β) : x ≍ y ↔ ∃ h : α = β, cast h x = y :=
--   ⟨λ | .rfl => ⟨rfl, rfl⟩, λ h ↦ match α, x, h with | _, _, ⟨rfl, rfl⟩ => .rfl⟩

-- example {p q : Prop} {α} {f : p → α} {g : q → α}
--     (hp : p := by (try constructor); (try assumption))
--     (hq : q := by (try constructor); (try assumption)) :
--       (f ≍ g ↔ (f hp = g hq)) :=
--   by obtain ⟨rfl, rfl⟩ := And.intro (eq_true hp) (eq_true hq); simp [funext_iff]



set_option genInjectivity false in
structure Extended (α : Type _) where
  IsFinite' : Prop
  get' : IsFinite' → α

namespace Extended
  variable
    {α β : Type _} {a a' : α} {b : β} {x y : Extended α}
    {p q : Prop} {f : p → α} {g : q → α}

scoped postfix:max "†" => Extended



section core

theorem mk.inj (h₁ : p ↔ q) (h₂ : ∀ hp hq, f hp = g hq) : mk p f = mk q g :=
  by obtain rfl := h₁.eq; obtain rfl := funext λ x ↦ h₂ x x; rfl

@[simp] theorem mk.inj_iff : (mk p f = mk q g) ↔ (p ↔ q) ∧ (∀ hp hq, f hp = g hq) := .intro
  (λ h ↦ h.ndrec
    (motive := λ x ↦ (p ↔ x.1) ∧ (∀ hp hq, f hp = x.2 hq))
    ⟨.rfl, λ _ _ ↦ rfl⟩)
  (λ ⟨h₁, h₂⟩ ↦ inj h₁ h₂)

@[coe] def finite (a : α) : α† := ⟨True, λ _ ↦ a⟩
  instance : Coe α α† where coe := finite

theorem finite_injective : (@finite α).Injective := λ _ _ h ↦ (mk.inj_iff.mp h).2 ⟨⟩ ⟨⟩

def Mem (self : α†) (a : α) : Prop := self = finite a
  instance : Membership α α† where mem := Mem

theorem mem_def : a ∈ x ↔ x = finite a := .rfl

theorem eq_of_mem_of_mem (h₁ : a ∈ x) (h₂ : a' ∈ x) : a = a' :=
  finite_injective $ h₁.symm.trans h₂

@[simp] theorem mem_mk_iff : a ∈ mk p f ↔ ∃ h, f h = a :=
  by simpa [mem_def, finite] using ⟨λ ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂ h₁⟩, λ ⟨h₁, h₂⟩ ↦ ⟨h₁, λ _ ↦ h₂⟩⟩

theorem mem_mk {h} : f h ∈ mk p f := mem_mk_iff.mpr ⟨_, rfl⟩

@[simp] theorem mem_finite_iff : a ∈ finite a' ↔ a = a' :=
  by simp [mem_def, finite, eq_comm]

theorem mem_finite : a ∈ finite a := mem_finite_iff.mpr rfl

@[ext low] def ext' (h : ∀ a, a ∈ x ↔ a ∈ y) : x = y :=
  match x, y with
  | ⟨p, f⟩, ⟨q, g⟩ => by
    obtain rfl : p = q := .propIntro
      (λ hp ↦ (by simpa using h (f hp):).1 hp |>.1)
      (λ hq ↦ (by simpa using h (g hq):).2 hq |>.1)
    obtain rfl : f = g := funext λ hp ↦
      (by simpa [hp] using h)
    rfl

def IsFinite (self : α†) : Prop := ∃ a, a ∈ self

theorem isFinite_def : x.IsFinite ↔ ∃ a, a ∈ x := .rfl

-- does `@[simp]` still apply if we remove `= True`?
@[simp] theorem isFinite_finite : (finite a).IsFinite = True := eq_true ⟨a, rfl⟩

@[simp] theorem isFinite'_iff_isFinite : x.IsFinite' ↔ x.IsFinite :=
  by rcases x; simp [isFinite_def, exists_comm]

@[simp, iff_back]
theorem isFinite_mk_iff : (mk p f).IsFinite ↔ p := isFinite'_iff_isFinite.symm

def get (self : α†) (h : self.IsFinite) : α := self.get' (isFinite'_iff_isFinite.mpr h)

@[simp] theorem get'_eq_get {h} : x.get' h = x.get (isFinite'_iff_isFinite.mp h) := rfl

@[simp] theorem get_mk {h} : get (mk p f) h = f (isFinite'_iff_isFinite.mpr h) := rfl

@[simp] theorem get_finite {h} : get ↑a h = a := rfl

@[simp] theorem finite_get {h} : ↑(x.get h) = x := by rcases h with ⟨a, hp, rfl⟩; rfl

@[elab_as_elim] def IsFinite.elim {motive : α† → _} (m : ∀ a, motive (finite a)) {x}
    (self : x.IsFinite) : motive x := x.finite_get ▸ m (x.get self)

@[ext] protected def ext
    (h₁ : x.IsFinite ↔ y.IsFinite)
    (h₂ : ∀ p q, x.get p = y.get q) : x = y :=
  ext' λ a ↦ .intro
    (by rintro rfl; simp_all [mem_def])
    (by rintro rfl; simp_all [mem_def, eq_comm])

@[simp] theorem get_eq_iff {h} : x.get h = a ↔ x = ↑a := by simp_all [Extended.ext_iff]

@[simp] theorem eq_get_iff {h} : a = x.get h ↔ ↑a = x := by simp_all [Extended.ext_iff]

theorem get_mem {h} : x.get h ∈ x := get_eq_iff.mp rfl

end core



section map
  variable {f : α → β}

def map (f : α → β) (x : α†) : β† := ⟨x.1, (f <| x.2 ·)⟩

@[simp, iff_back]
theorem mem_map_iff : b ∈ x.map f ↔ ∃ a ∈ x, b = f a :=
  by rcases x with ⟨p, x⟩; simp (contextual := true) [map, mem_def, finite, and_assoc, eq_comm]

@[simp] theorem map_finite : map f ↑a = ↑(f a) := rfl

@[simp] theorem map_isFinite : (x.map f).IsFinite ↔ x.IsFinite :=
  by simp [isFinite_def, exists_comm]

@[simp] theorem get_map {h} : (x.map f).get h = f (x.get (map_isFinite.mp h)) := rfl

end map



section bind
  variable {f : α → β†}

def bind (x : α†) (f : α → β†) : β† := ⟨∃ h, (f (x.2 h)).1, λ h ↦ (f _).2 h.2⟩

@[simp, iff_back]
theorem mem_bind_iff : b ∈ x.bind f ↔ ∃ a ∈ x, b ∈ f a := by
  obtain ⟨f₁, f₂, rfl⟩ :
    (f₁ : α → Prop) × {f₂ : ∀ a, (f₁ a) → β // f = λ a ↦ ⟨f₁ a, f₂ a⟩} :=
      ⟨_, _, funext λ a ↦ rfl⟩
  rcases x with ⟨p, x⟩
  simp (contextual := true) [-get'_eq_get, bind, mem_def,
      finite, and_assoc, iff_iff_implies_and_implies, And.forall]

@[simp] theorem bind_finite : bind ↑a f = f a := ext' (by simp)

@[simp] theorem bind_isFinite : (x.bind f).IsFinite ↔ ∃ a ∈ x, (f a).IsFinite :=
  by simp [isFinite_def, exists_comm]

theorem isFinite_of_bind (h : (x.bind f).IsFinite) : x.IsFinite :=
  (bind_isFinite.mp h).imp λ _ ⟨_, _⟩ ↦ ‹_›

theorem isFinite_apply_of_bind (h₁ : (x.bind f).IsFinite) {h₂} : (f (x.get h₂)).IsFinite :=
  by obtain ⟨_, rfl, _⟩ := bind_isFinite.mp h₁; simp_all

@[simp] theorem get_bind {h} :
    (x.bind f).get h = (f (x.get (isFinite_of_bind h))).get (isFinite_apply_of_bind h) := rfl

end bind



section monad

instance : Monad Extended where
  pure := finite
  bind := bind
  map  := map

instance : LawfulMonad Extended := .mk'
  (id_map         := by intros; rfl)
  (pure_bind      := by intros; ext <;> simp [Bind.bind, Pure.pure])
  (bind_pure_comp := by intros; ext <;> simp [Bind.bind, Pure.pure, Functor.map, isFinite_def])
  (bind_assoc     := by intros; ext <;> simp [Bind.bind, ←exists_and_left, ←exists_and_right,
      and_assoc, exists_comm (α := type_of% (‹_†›.get _))])

end monad



-- TODO: why does `to_additive` not work here? (investigate how `Part` achives this)
-- I have left this code as it 'should be', even though `to_additive` does nothing
-- For that matter, `to_additive` should warn if the (main) declaration comes back unchanged
section classes

@[to_additive] instance [Mul α] : Mul α† where mul x y := x.bind λ x ↦ y.map λ y ↦ x * y

@[to_additive (attr := simp, iff_back)]
theorem mem_mul_iff {c} [Mul α] : c ∈ x * y ↔ ∃ a ∈ x, ∃ b ∈ y, c = a * b :=
  by simp [HMul.hMul, Mul.mul]

@[to_additive (attr := simp)]
theorem mul_isFinite [Mul α] : (x * y).IsFinite ↔ x.IsFinite ∧ y.IsFinite :=
  by simp [HMul.hMul, Mul.mul, ←isFinite_def]

@[to_additive (attr := simp)]
theorem get_mul [Mul α] {h} :
    (x * y).get h = x.get (mul_isFinite.mp h).1 * y.get (mul_isFinite.mp h).2 := rfl

@[to_additive (attr := simp)]
theorem finite_mul_finite {a b : α} [Mul α] : (a : α†) * (b : α†) = (a * b : α) :=
  by ext <;> simp

end classes



section le

instance [LE α] : LE α† where
  le x y := ∀ b ∈ y, ∃ a ∈ x, a ≤ b

theorem le_finite_iff [LE α] : x ≤ ↑a ↔ ∃ b ∈ x, b ≤ a :=
  ⟨λ h ↦ h a rfl, λ ⟨b, h₁, h₂⟩ _ h ↦ ⟨b, h₁, mem_finite_iff.mp h ▸ h₂⟩⟩

theorem finite_le_iff [LE α] : ↑a ≤ x ↔ ∀ b ∈ x, a ≤ b := .intro
  (λ h a ha ↦ (h a ha).elim λ _ ⟨h₁, h₂⟩ ↦ mem_finite_iff.mp h₁ ▸ h₂)
  (λ h b hb ↦ ⟨a, rfl, h b hb⟩)

@[simp, iff_back]
theorem finite_le_finite_iff [LE α] : finite a ≤ finite a' ↔ a ≤ a' :=
  by simp [le_finite_iff]

theorem get_le_iff [LE α] {h} : x.get h ≤ a ↔ x ≤ ↑a :=
  by rw [←finite_le_finite_iff, finite_get]

theorem le_get_iff [LE α] {h} : a ≤ x.get h ↔ ↑a ≤ x :=
  by rw [←finite_le_finite_iff, finite_get]

@[simp, iff_back]
theorem get_le_get_iff [LE α] {hx hy} : x.get hx ≤ y.get hy ↔ x ≤ y :=
  by rw [get_le_iff, finite_get]

end le

section preorder

instance [Preorder α] : Preorder α† where
  --lt x y := ∃ a ∈ x, ∀ b ∈ y, a < b -- actually need local decidability here...
  le_refl x a h := ⟨a, h, le_rfl⟩
  le_trans := by
    rintro ⟨p, f⟩ ⟨q, g⟩ ⟨r, h⟩
    simpa [LE.le] using λ h₁ h₂ hr ↦ (h₂ hr).elim λ hq h₂ ↦ (h₁ hq).imp λ hp h₁ ↦ le_trans h₁ h₂

theorem lt_finite_iff [Preorder α] : x < ↑a ↔ ∃ b ∈ x, b < a :=
  by simp (contextual := true) only [
    lt_iff_le_not_ge, mem_def,
    le_finite_iff (x:=x), finite_le_finite_iff,
    ←exists_and_right, ←exists_prop (a:=x=_)
  ]

theorem finite_lt_iff [Preorder α] : ↑a < x ↔ ∀ b ∈ x, a < b :=
  by simp [lt_iff_le_not_ge, finite_le_iff, mem_def, le_finite_iff, forall_and];

@[simp, iff_back]
theorem finite_lt_finite_iff [Preorder α] : finite a < finite a' ↔ a < a' :=
  by simp [lt_finite_iff]

theorem get_lt_iff [Preorder α] {h} : x.get h < a ↔ x < ↑a :=
  by rw [←finite_lt_finite_iff, finite_get]

theorem lt_get_iff [Preorder α] {h} : a < x.get h ↔ ↑a < x :=
  by rw [←finite_lt_finite_iff, finite_get]

@[simp, iff_back]
theorem get_lt_get_iff [Preorder α] {hx hy} : x.get hx < y.get hy ↔ x < y :=
  by rw [get_lt_iff, finite_get]

theorem monotone_finite [Preorder α] : Monotone (.finite : α → α†) :=
  λ _ _ ↦ finite_le_finite

theorem strictMono_finite [Preorder α] : StrictMono (.finite : α → α†) :=
  λ _ _ ↦ finite_lt_finite

end preorder

section partialOrder

instance [PartialOrder α] : PartialOrder α† where
  le_antisymm := by
    rintro ⟨_, _⟩ ⟨_, _⟩
    simp_rw [LE.le, mem_mk_iff, exists_exists_eq_and,
        forall_exists_index, forall_apply_eq_imp_iff]
    refine λ h₁ h₂ ↦ Extended.ext' λ _ ↦ ⟨?_, ?_⟩ <;>
    · rintro ⟨_, _⟩
      revert h₁ h₂
      simp_rw [exists_const, forall_const, mem_mk_iff, forall_exists_index]
      intros
      exact ⟨‹_›, le_antisymm ‹_› $ ‹_ → _› ‹_›⟩

end partialOrder



-- theorem finite_of_lt [Preorder α] (l₁ l₂ : α†) : l₁ < l₂ → ∃ a : α, l₁ = ↑n :=
--   λ ⟨_, ⟨h, _⟩, _⟩ ↦ ⟨l₁.get h, by simp [Extended.finite]⟩

-- theorem finite_of_le [Preorder α] (x : α†) (a : α) (h : x ≤ ↑n) : ∃ b : α, x = ↑m :=
--   (h a ⟨⟨⟩, rfl⟩).imp λ _ ⟨h, _⟩ ↦ Part.eq_some_iff.mpr h

-- theorem lt_iff_add_one_le [Preorder α] : (l₁ l₂ : α†) → l₁ < l₂ → l₁ + 1 ≤ l₂
--   | ⟨p, x⟩, ⟨q, y⟩, ⟨_, ⟨p, rfl⟩, h⟩, _, ⟨q, rfl⟩ =>
--       ⟨(x p)+1, ⟨⟨p, ⟨⟩⟩, rfl⟩, h (y q) ⟨q, rfl⟩⟩

end Extended
