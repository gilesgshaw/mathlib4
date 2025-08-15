import Mathlib.Order.Basic

/-
# Thoughts about IO

## How do we capture the notation that time moves 'forwards'?

The 'ideal' approach here is probably that we should redefine IO in terms of functions
`RealWorld → RealWorld` satisfying some opaque predicate `p`. Then, e.g. we can stipulate that
there is a function `time : RealWorld → Time` such that `∀ x f, p f → time x ≤ time f x`.

We could also use this to prove that certain values `x : RealWorld` are not 'reachable' at all.


## How do we capture the notation of sleeping?

Perhaps this just means that `RealWorld` contains information about how much time has passed.
Is there also a state that corresponds to blocking indefinately?

## How do we capture the notation of possible non-termination?

We have tried creating a monad to this effect in two different ways.
The first way is via the monad `α ↦ {f : α → Nat // 'once some, is constant' }`
The second way is via the monad `α ↦ (σ : Type) × (init : σ ⊕ α) × (f : σ → σ ⊕ α)`

Note that, wheras constructs like `repeat` and `partial` are currently opaque in the type-theoretic
sense, if `IO` were to incorperate formally this notion, we would improve the situation.
That is, a `partial` function could actually be a function incorperating the 'partial' monad.
Then, to 'evaluate' a `partial` function, we just need to lift this to `IO`.
In order for this to be efficient, it looks like the second way would be preferable.
Nonetheless, something of the efficiency of the compiler will probably be lost anyway.
-/

namespace IO

-- preorder??
-- might not need at all, as we can make assertions about evolution on a case-by-case basis?
local instance : Inhabited $ PartialOrder RealWorld where
  default.le                  := Eq
  default.le_refl             := Eq.refl
  default.le_trans _ _ _      := Eq.trans
  default.le_antisymm _ _ _ _ := ‹_› in
@[instance] opaque partialOrderRealWorld : PartialOrder RealWorld

end IO

def FEIO (ε α : Type) := (s₀ : IO.RealWorld) → EStateM.Result ε {s // s₀ ≤ s} α

instance (ε : Type) : Monad (FEIO ε) where
  pure x s := .ok x ⟨s, le_rfl⟩
  bind x f r :=
    match x r with
    | .error e s => .error e s
    | .ok y s    =>
      match f y s with
      | .error e t => .error e t
      | .ok z t    => .ok z ⟨t, s.2.trans t.2⟩

instance (ε : Type) : MonadLift (FEIO ε) (EIO ε) where
  monadLift k s := match k s with
    | .ok    r s => .ok    r ↑s
    | .error r s => .error r ↑s
