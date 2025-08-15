import Mathlib.Tactic.Linter
set_option linter.style.commandStart false
set_option linter.style.lambdaSyntax false

local notation "Byte" => UInt8
local notation "Byte?" => Option Byte

structure DelayedInterface where
  Delayed : Type → Type
  monad : Monad Delayed
  mem {α} : Membership α (Delayed α)
  consistent {α} (x : Delayed α) : ∀ a ∈ x, ∀ b ∈ x, a = b
  liftIO : MonadLift Delayed IO
  get_mem {α} (x : Delayed α) : Delayed {a // a ∈ x}
  bind' {α β} (k : Delayed α) (f : (x : α) → (x ∈ k) → Delayed β) : Delayed β
    := bind (get_mem k) λ x ↦ f x.1 x.2

instance : Inhabited DelayedInterface where default := {
  Delayed    := Id
  monad      := inferInstance
  liftIO     := ⟨pure⟩
  mem        := ⟨Eq⟩
  consistent := λ _ _ h₁ _ h₂ ↦ h₁.symm.trans h₂
  get_mem    := λ x ↦ ⟨x, rfl⟩
}

unsafe def DelayedImp : DelayedInterface where
  Delayed    := IO
  monad      := inferInstance
  liftIO     := ⟨id⟩
  mem        := ⟨λ _ _ ↦ True⟩
  consistent := lcProof
  get_mem    x := x.map λ x ↦ ⟨x, True.intro⟩

@[implemented_by DelayedImp]
opaque DelayedDef : DelayedInterface



def Delayed := DelayedDef.Delayed
instance : Monad Delayed := DelayedDef.monad
instance : MonadLift Delayed IO := DelayedDef.liftIO
instance {α} : Membership α (Delayed α) := DelayedDef.mem



structure StreamModel (χ : Type) where
  get : Nat → Delayed (Array χ)
  cons : ∀ n m, n ≤ m → ∀ xs ∈ get n, ∀ ys ∈ get m, xs

namespace StreamModel
  variable (self : StreamModel)

def putBack (arr : ByteArray) : StreamModel where
  _

end StreamModel



structure IStream where
  read    : USize → Delayed ByteArray
  deriving Inhabited








namespace IO

structure StreamInterface where
  α : Type
  c : α → IO (Byte × α)

-- IO (Byte × prev)


-- stream which may give data in `ByteArray` chunks as an IO operation
/-
Reads up to the given number of bytes from the handle; fewer indicates EOF.
Encountering an EOF does not close a handle; subsequent reads may block and return more data.
-/

structure OngoingStream where
  _


-- like a stack
structure IStream where
  request (n : USize) : Task Unit
  putBack (xs : ByteArray) : Unit
  available                : USize
  seek  (i : ISize)        : Task Unit         -- does not cause error until trying to read
  read? (n : USize)        : Task ByteArray
  peek? (n : USize)        : Task ByteArray

  deriving Inhabited

end IO
