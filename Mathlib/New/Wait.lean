


/-
Consider the official spesification of the `IO.FS` method `Stream.read count : IO ByteArray`.
If the requested amount of data is not currently available, we understand that either/both of
the following may happen
* The request will block, possibly waiting for user input
* The request will return less data than requested.

It is stipulated that an empty return indicates an `EOF` marker, though it is not clear wherther
this applies more generally to a return with fewer bytes than requested. In any case, this seems
to be a moot point, as we understand an `EOF` marker not to mean per-se that no more data is
available, but rather that that no more data is available without blocking.

We assume that whenever the method can return the requested number of bytes without blocking, it
will do so. In fact, it seems likely that the method will not block.

At the end of the day, 'advancement' is non-deterministic.

Eof
Blocking

An `EOF` marker indicates that there is no more data available currently, but there may be in the
future.

Blocking indicates


 appears to be
as follows:

If there is any data available without blocking, do not wait for more to become available.

If there is not any data

An EOF does not actually close a stream, so further reads may block and return more data.

Our notation of `Law` is in keeping with actions monadic in `IO` being 'nondeterministic'.
That is,

-/

open IO (RealWorld Ref)

structure Law (σ α) where
  Valid (before after : σ) (result : α) : Prop

def Law.post {σ} : Law σ σ where
  Valid _ after result := after = result

-- note, we have ignored FEIO here, and not required state to be order hom...
-- because perhaps this is enforced in the law itself...
def IsLawful {ε σ α} (k : EIO ε α) (law : Law σ α) (state : RealWorld → σ) :=
  (before : RealWorld) →
    match k before with
    | .ok result after => law.Valid (state before) (state after) result
    | _ => True




variable {χ : Type _}

-- could also implement `readToEnd`, if we disallow an 'infinite' state, or somehow incorperate
-- lack of termination into the model for `IO`
structure StreamInterface χ ε where
  read (count : Nat) : EIO ε (List χ)
  peek (count : Nat) : Option (EIO ε (List χ))

structure StreamWrapper χ ε where
  base : StreamInterface χ ε
  buffer : Ref (List χ)

namespace StreamWrapper

variable {ε} (self : StreamWrapper χ ε)

-- def readIntoBuffer (count : Nat) : EIO ε Unit := do
--   let data ← self.base.read count
--   self.buffer.modify λ x ↦ x.append data

def toIntf : StreamInterface χ ε where
  read count :=
    self.buffer.modifyGet λ buf ↦
      let count := min count buf.length
      (buf.extract 0 count, buf.extract count buf.length)
  peek count := some $
    self.buffer.get <&> λ buf ↦
      let count := min count buf.length
      buf.extract 0 count

end StreamWrapper








-- could we actually just 'forget' the bytes already read??
structure StrState (χ : Type _) where
  data  : FormalStream χ
  pos   : Nat
  valid : -- don't need to enforece, as we can consider some real world states 'invalid'?
    pos ≤ data.length

namespace StrState
  variable (self : StrState χ)

-- def prepend (data : List χ) : StrState χ where
--   data  := ↑data ++ self.data
--   pos   := data.length + self.pos
--   valid := by
--     simp
--     _

end StrState

def StreamReadLaw (count : Nat) : Law (StrState χ) (List χ) where
  Valid before after result :=
    result = (after.data |>.drop before.pos |>.take count) ∧
    after.pos = before.pos + result.length

def StreamPeekLaw (count : Nat) : Law (StrState χ) (List χ) where
  Valid before after result :=
    result = (after.data |>.drop before.pos |>.take count) ∧
    after.pos = before.pos

structure StreamModel {ε} (i : StreamInterface χ ε) (state : RealWorld →StrState χ) where
  lawfulRead count : IsLawful (i.read count) (StreamReadLaw count) state
  lawfulPeek count : ∀ peek' ∈ i.peek count, IsLawful peek' (StreamPeekLaw count) state

--theorem ggg {σ m} [MonadLiftT (ST σ) m] {α : Type} (r : ST.Ref σ α) : m α

axiom get_basis {σ α} (r : ST.Ref σ α) : σ → α
axiom set_basis {σ α} (r : ST.Ref σ α) : α → σ → σ

axiom ss {σ α} (r : ST.Ref σ α) (s : σ) :
  ST.Prim.Ref.get r s = .ok (get_basis r s) s

axiom ss1 {σ α} (r : ST.Ref σ α) (s : σ) (a : α) :
  ST.Prim.Ref.set r a s = .ok () (set_basis r a s)

-- theorem gg {ε} (i : StreamInterface χ ε) (buf : Ref (List χ)) (state : RealWorld → StrState χ)
--     (h : StreamModel i state) : StreamModel (StreamWrapper.toIntf ⟨i, buf⟩)
--     (λ w ↦ state w) where
--   lawfulPeek count :=
--     λ f h w ↦ by
--       simp [StreamWrapper.toIntf, ST.Ref.get, liftM, monadLift, MonadLift.monadLift] at h
--       subst h
--       unfold BaseIO.toEIO
--       simp [ss, Functor.mapRev, Functor.map, EStateM.map, StreamPeekLaw]
--       have := h.lawfulPeek count
--       _
--   lawfulRead count :=
--     λ w ↦ by
--       simp [StreamWrapper.toIntf]
--       have := h.lawfulRead
--       _
