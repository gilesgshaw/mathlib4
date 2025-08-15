namespace IO

local notation "Byte" => UInt8
local notation "Byte?" => Option Byte

def ensure {ε m} [Monad m] [MonadExcept ε m] {α}
    (p : α → Prop) [DecidablePred p] (e : ε) (f : m α) : m α :=
  f >>= λ x ↦ if p x then return x else throw e




structure FS.BIStream where
  putBack (xs : ByteArray) : IO Unit
  seek  (i : ISize) : IO Unit         -- does not cause error until trying to read
  read? (n : USize) : IO ByteArray
  peek? (n : USize) : IO ByteArray

  read! (n : USize) : IO ByteArray := ensure (·.size = n.1) .unexpectedEof <| read? n
  readByte?         : IO Byte?     := (·.toList.head?) <$> read? 1
  readByte!         : IO Byte      := (·.toList.head!) <$> read! 1
  peek! (n : USize) : IO ByteArray := ensure (·.size = n.1) .unexpectedEof <| peek? n
  peekByte?         : IO Byte?     := (·.toList.head?) <$> peek? 1
  peekByte!         : IO Byte      := (·.toList.head!) <$> peek! 1
  deriving Inhabited




structure FS.Buffer where
  data : ByteArray
  pos : ISize

namespace FS.Buffer

variable (self : Buffer)

def length : ISize := .ofInt self.data.size

def remaining : ISize := self.length - self.pos

def seek (i : ISize) : Buffer := ⟨self.data, self.pos + i⟩

def append (a : ByteArray) : Buffer := ⟨self.data.append a, self.pos⟩


def validPos : Prop := 0 ≤ self.pos ∧ self.pos ≤ self.length

instance : Decidable self.validPos := by unfold validPos; infer_instance

def extract (n : USize) : (h₁ : self.validPos) → (h₂ : (self.seek n.toISize).validPos) → ByteArray :=
  λ _ _ ↦ self.data.extract self.pos.toNatClampNeg (self.pos.toNatClampNeg + n.toNat)

end FS.Buffer


structure FS.BStream where
  base   : Stream
  buffer : Ref Buffer
  window : USize := 4

def FS.BStream.toBIStream (self : BStream) (str : BStream) : BIStream where
  seek n := do
    if (←self.buffer.get).remaining < n then
      let data ← self.base.read (max n.toUSize self.window)
      self.buffer.modify (·.append data)
    if (←self.buffer.get).remaining < n then throw .unexpectedEof
    self.buffer.modify λ buf ↦ buf.seek n

  peek? n := do
    if (←self.buffer.get).remaining < n.toISize then
      let data ← self.base.read (max n self.window)
      self.buffer.modify (·.append data)
    --if (←self.buffer.get).remaining < n then throw .unexpectedEof
    return (←self.buffer.get).extract n _ _


  read? n := do
    _ --let available ← str.request n
    --return ←str.copyFromBuffer (min available n)

  putBack := _









-- returned contains first violation, unless end is reached
def readWhile (self : BIStream) (p : Byte → Bool) : IO ByteArray := do
  let mut result := .empty
  repeat
    let c ← self.read 1
    result := result.append c
    if ∀ _, !p c[0] then break
  return result

-- returned contains first violation, unless end is reached
def readUntil (self : BIStream) (p : Byte → Bool) : IO ByteArray := do
  let mut result := .empty
  repeat
    let c ← self.read 1
    result := result.append c
    if ∀ _, p c[0] then break
  return result


end IO
