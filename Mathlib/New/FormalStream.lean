import Mathlib.New.«Extended.Find»
open Extended

theorem dite_eq_iff''' {α} {P : Prop} [Decidable P] {c : α} {A B} :
    dite P A B = c ↔ (∀ h, A h = c) ∧ ∀ h, B h = c :=
  ⟨fun he ↦ ⟨fun h ↦ (dif_pos h).symm.trans he, fun h ↦ (dif_neg h).symm.trans he⟩, fun he ↦
    (Decidable.em P).elim (fun h ↦ (dif_pos h).trans <| he.1 h) fun h ↦ (dif_neg h).trans <| he.2 h⟩

@[simp high] lemma Nat.find_le_iff' {p : Nat → Prop} [DecidablePred p] (i) :
    (∃ (h : ∃ i, p i), Nat.find h ≤ i) ↔ ∃ j ≤ i, p j :=
  by simpa [Nat.find_le_iff] using by intros; constructor; assumption

instance {α} (x : Option α) : Decidable (x = none) :=
  decidable_of_iff x.isNone x.isNone_iff_eq_none

def Stream.nth? {α χ} [Stream α χ] (str : α) (i : Nat) : Option (χ × α) :=
  next? str |> i.repeat λ str ↦
      str.bind (next? ·.2)

theorem Stream.nth?_mono {α χ} [Stream α χ] (str : α) {i j} (heq : nth? str i = none) :
    (hle : i ≤ j := by omega) → nth? str j = none
  | .refl => heq
  | .step hle =>
      Option.bind_eq_none_iff.mpr
        λ r h' ↦ Option.some_ne_none r (nth?_mono str heq hle |> .trans h'.symm) |>.elim

def Stream.get? {α χ} [Stream α χ] (str : α) (i : Nat) : Option χ :=
  (nth? str i).map Prod.fst

theorem Stream.get?_mono {α χ} [Stream α χ] (str : α) ⦃i j⦄ (heq : get? str i = none)
    (hle : i ≤ j := by omega) : get? str j = none :=
  Option.map_eq_none_iff.mpr <| (nth?_mono str)
    <| Option.map_eq_none_iff.mp <| heq

theorem Stream.get?_mono' {α χ} [Stream α χ] (str : α) ⦃i j⦄
    (hle : i ≤ j) (heq : get? str i = none) : get? str j = none :=
  Option.map_eq_none_iff.mpr <| (nth?_mono str)
    <| Option.map_eq_none_iff.mp <| heq



-- @[to_additive (attr := simp)]
-- theorem Part.mem_mul_iff {α} [Mul α] (x y : Part α) (c : α) :
--     c ∈ (x * y) ↔ ∃ a ∈ x, ∃ b ∈ y, a * b = c :=
--   mem_bind_iff.trans $ by simp [mem_map_iff]

structure FormalStream (χ) where
  /-- For most purpouses, `str[i]?` should be used instead -/
  get?  : Nat → Option χ
  _mono : ∀ ⦃i j⦄, (hle : i ≤ j) → (heq : get? i = none) → get? j = none

namespace FormalStream
  variable {χ : Type _}

def length (s : FormalStream χ) : Nat† := .find (s.get? · = none)

instance instGetElem? : GetElem? (FormalStream χ) (Nat) (χ) (λ str i ↦ i < str.length) where
  getElem? str     := str.get?
  getElem  str i h := str.get? i |>.get (Option.isSome_iff_ne_none.mpr $ not_of_lt_find h)

@[simp] theorem get?_eq_getElem? {str : FormalStream χ} {i : Nat} : str.get? i = str[i]? := rfl

attribute [deprecated "test" (since := "2025-08-13")] get?

def mono (self : FormalStream χ) ⦃i j : Nat⦄
  (heq : self[i]? = none) (hle : i ≤ j := by omega) : self[j]? = none := self._mono hle heq

def mono' (self : FormalStream χ) ⦃i j : Nat⦄ (hle : i ≤ j)
  (heq : self[i]? = none) : self[j]? = none := self._mono hle heq

attribute [deprecated "test" (since := "2025-08-13")] _mono




section length
  variable {s : FormalStream χ} {i : Nat}

theorem length_isFinite_iff : s.length.IsFinite ↔ ∃ i : Nat, s[i]? = none := find_isFinite_iff

@[simp] theorem get_get_length_eq_none {h} : s[s.length.get h]? = none :=
  find_spec_get (h:=h)

@[iff_forw none_of_length_le, iff_back length_le_of_none]
theorem length_le_iff : s.length ≤ ↑i ↔ s[i]? = none := find_le_iff' s.mono'

@[iff_back lt_length_of_isSome, iff_forw isSome_of_lt_length]
theorem lt_length_iff : ↑i < s.length ↔ s[i]?.isSome :=
  lt_find_iff' s.mono' |>.trans Option.isSome_iff_ne_none.symm

theorem length_lt_iff : s.length < ↑i ↔ ∃ j < i, s[j]? = none :=
  find_lt_iff

theorem le_length_iff : ↑i ≤ s.length ↔ ∀ j < i, s[j]?.isSome :=
  by simp_rw [length, le_find_iff, Option.ne_none_iff_isSome, getElem?]

theorem length_eq_iff : s.length = ↑i ↔ s[i]? = none ∧ ∀ j < i, s[j]?.isSome :=
  by simp_rw [length, find_eq_iff, Option.ne_none_iff_isSome, getElem?]

theorem eq_length_iff : ↑i = s.length ↔ s[i]? = none ∧ ∀ j < i, s[j]?.isSome :=
  by simp_rw [length, eq_find_iff, Option.ne_none_iff_isSome, getElem?]

theorem mem_length_iff : i ∈ s.length ↔ s[i]? = none ∧ ∀ j < i, s[j]?.isSome :=
  by simp_rw [length, mem_find_iff, Option.ne_none_iff_isSome, getElem?]

end length



instance {str : FormalStream χ} {i : Nat} : Decidable (↑i < str.length) :=
  decidable_of_iff' str[i]?.isSome lt_length_iff

instance {str : FormalStream χ} {i : Nat} : Decidable (↑i ≤ str.length) :=
  decidable_of_iff' (∀ j < i, str[j]?.isSome) le_length_iff

instance : LawfulGetElem (FormalStream χ) (Nat) (χ) (λ str i ↦ ↑i < str.length) where
  getElem?_def str i h := .symm $ dite_eq_iff'''.mpr ⟨λ _ ↦ Option.some_get _,
    λ h ↦ .symm $ Decidable.of_not_not λ hc ↦ h
      $ lt_length_of_isSome $ Option.isSome_iff_ne_none.mpr hc⟩

@[ext] protected theorem ext {x y : FormalStream χ} (h : ∀ i : Nat, x[i]? = y[i]?) : x = y :=
  match x, y, funext h with | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

-- pri??
@[ext] protected theorem ext' {x y : FormalStream χ}
    (h₁ : x.length = y.length) (h₂ : ∀ (i : Nat) _ _, x[i] = y[i]) : x = y :=
  by ext i; by_cases i < x.length <;> simp_all

def IsPrefix (x y : FormalStream χ) : Prop := ∀ ⦃i : Nat⦄ ⦃a⦄, a ∈ x[i]? → a ∈ y[i]?

def drop (count : Nat) (self : FormalStream χ) : FormalStream χ :=
  ⟨λ i ↦ self[count + i]?, λ _ _ _ h ↦ self.mono h⟩

def next? (self : FormalStream χ) : Option (χ × FormalStream χ) :=
  self[0]? <&> (·, self.drop 1)

instance : Stream (FormalStream χ) χ := {next?}

@[simp] theorem get_drop {self : FormalStream χ} {i j : Nat} :
  (self.drop i)[j]? = self[i + j]? := rfl


def take (count : Nat) (self : FormalStream χ) : List χ :=
  match count, self[0]? with
  | c+1, some x => x :: (self.drop 1).take c
  | _,   _      => []

instance : PartialOrder (FormalStream χ) where
  le                         := IsPrefix
  le_refl x i a h            := h
  le_trans x y z h₁ h₂ i a h := h₂ (h₁ h)
  le_antisymm x y h₁ h₂      := x.ext λ i ↦ Option.ext λ a ↦ ⟨(h₁ ·), (h₂ ·)⟩

theorem mono_drop {count : Nat} : Monotone (drop (χ:=χ) count) :=
  λ _ _ h₁ _ _ h₂ ↦ h₁ h₂



def ofStream {α} [Stream α χ] (x : α) : FormalStream χ where
  get?  := Stream.get? x
  _mono := Stream.get?_mono' x

def join_aux : (l : List (FormalStream χ)) → Option (χ × List (FormalStream χ))
  | []   => none
  | h::t =>
    (h.next?.map λ (x, h) ↦ (x, h::t)) <|> join_aux t

-- theorem length_join_aux {l : List (FormalStream χ)} :
--     ∀ r ∈ join_aux l, (r.2.map length).sum + 1 = (l.map length).sum :=
--   _

instance : Stream (List (FormalStream χ)) χ where next? := join_aux

def join : (l : List (FormalStream χ)) → FormalStream χ := .ofStream

-- example (self : FormalStream χ) : ofStream self = self :=
--   _

-- theorem length_join {l : List (FormalStream χ)} :
--     (join l).length = (l.map length).sum := by
--   _

def append (l r : FormalStream χ) : FormalStream χ := .join [l, r]

instance : Append (FormalStream χ) := {append}

-- configure simps...
@[simps, coe] def ofList (l : List χ) : FormalStream χ where
  get? i := l[i]?
  _mono  := by simp_rw [List.getElem?_eq_none_iff]; omega

instance : Coe (List χ) (FormalStream χ) where coe := ofList

-- @[simp] theorem length_ofList {l : List χ} : length (ofList l) = ↑l.length :=
--   by simp [length_eq_iff]; _

end FormalStream
