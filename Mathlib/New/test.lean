import Lean
open IO
open Lean

structure IO.Process.BinOutput where
  /-- The process's exit code. -/
  exitCode : UInt32
  /-- Everything that was written to the process's standard output. -/
  stdout   : ByteArray
  /-- Everything that was written to the process's standard error. -/
  stderr   : String


-- currently, we have the broken pipe error if exists during input
-- flushes, and sends EOF
/--
Runs a process to completion and captures its output and exit code. Immediately after the child
process is spawned, a handle to its standard input is passed to the function `k`. Once control has
returned from `k`, the current process blocks until the child process has run to completion.

The specifications of standard input, output, and error handles in `args` are ignored.
-/
def IO.Process.output' (args : SpawnArgs) (k : (stdin : FS.Handle) → IO Unit) : IO Output := do
  let child ← spawn {args with stdout := .piped, stderr := .piped, stdin := .piped}
  k child.stdin
  child.stdin.flush
  let (_, child) ← child.takeStdin
  let stdout ← IO.asTask child.stdout.readToEnd .dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  let stdout ← IO.ofExcept stdout.get
  return {exitCode, stdout, stderr}

def IO.Process.output'' (args : SpawnArgs) (k : (stdin : FS.Handle) → IO Unit) : IO BinOutput := do
  let child ← spawn {args with stdout := .piped, stderr := .piped, stdin := .piped}
  k child.stdin
  child.stdin.flush
  let (_, child) ← child.takeStdin
  let stdout ← IO.asTask child.stdout.readBinToEnd .dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  let stdout ← IO.ofExcept stdout.get
  return {exitCode, stdout, stderr}


/--
If `output` has exit code 0, its standard output is returned.
Otherwise an exception is thrown using `descr` to describe the process.
-/
def IO.Process.Output.result! (descr : String) (output : Output) : IO String := do
  if output.exitCode = 0 then return output.stdout
  throw <| .userError s!
    "process\n  \
      {descr}\n\
    exited with code {output.exitCode}\n  \
      {output.stderr}"

def IO.Process.BinOutput.result! (descr : String) (output : BinOutput) : IO ByteArray := do
  if output.exitCode = 0 then return output.stdout
  throw <| .userError s!
    "process\n  \
      {descr}\n\
    exited with code {output.exitCode}\n  \
      {output.stderr}"


def IO.Process.run' (args : SpawnArgs) (k : (stdin : FS.Handle) → IO Unit) : IO String :=
  output' args k >>= Output.result! (args.cmd |> args.args.foldl (·++" "++·))

def IO.Process.run'' (args : SpawnArgs) (k : (stdin : FS.Handle) → IO Unit) : IO ByteArray :=
  output'' args k >>= BinOutput.result! (args.cmd |> args.args.foldl (·++" "++·))

def IO.Process.run''' (args : SpawnArgs) (k : (stdin : FS.Handle) → IO Unit) : IO FS.Handle := do
  let child ← spawn {args with stdout := .piped, stderr := .piped, stdin := .piped}
  k child.stdin
  child.stdin.flush
  let (_, child) ← child.takeStdin
  --let stdout ← IO.asTask child.stdout.readBinToEnd .dedicated
  --let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  --let stdout ← IO.ofExcept stdout.get
  if exitCode = 0 then return child.stdout
  throw <| .userError s!
    "process\n  \
      {args.cmd |> args.args.foldl (·++" "++·)}\n\
    exited with code {exitCode}\n  \
      {←child.stderr.readToEnd}"

/-
lake exe cache get
lake exe mk_all
for pr, make sure to base off a commit recognised downstream
synchronisation of lean version
-/


open Lean System

structure Hash where
  toString : String
  deriving Hashable, DecidableEq, Repr

instance : Inhabited Hash where default := ⟨"INHABITED HASH"⟩
instance : ToMessageData Hash where toMessageData x := x.toString

def sha1 (data : ByteArray) : IO Hash := do
  let result ← Process.run' {cmd := "sha1sum"} (·.write data)
  if result.length ≠ 44 ∨ result.drop 40 ≠ " *-\n" then
    throw <| .userError "unexpected output from 'sha1sum'"
  return ⟨result.take 40⟩

def inflate (data : ByteArray) : IO ByteArray := do
  let hexStr : String := "" |> data.foldl
    λ s x ↦ s! "{s}{hexDigitRepr (x.toNat/16)}{hexDigitRepr (x.toNat%16)}"
  return ←Process.run'' {cmd := "python"}
    λ h ↦ h.putStr s! "\
      import zlib\n\
      import sys\n\
      sys.stdout.buffer.write(zlib.decompress(bytes.fromhex(\"{hexStr}\")))\n\
    "

def inflate' (data : ByteArray) : IO FS.Handle := do
  let hexStr : String := "" |> data.foldl
    λ s x ↦ s! "{s}{hexDigitRepr (x.toNat/16)}{hexDigitRepr (x.toNat%16)}"
  return ←Process.run''' {cmd := "python"}
    λ h ↦ h.putStr s! "\
      import zlib\n\
      import sys\n\
      sys.stdout.buffer.write(zlib.decompress(bytes.fromhex(\"{hexStr}\")))\n\
    "





structure Git where
  mainDir : FilePath := "C:\\Users\\Giles\\lean4\\cpp\\.git"

namespace Git

variable (git : Git)

def objDir : FilePath := git.mainDir.join "objects"

def objs : IO (Array Hash) := do
  let mut result := #[]
  for subDir in ←git.objDir.readDir do
    if ←subDir.path.isDir then
      for obj in ←subDir.path.readDir do
        result := result.push ⟨subDir.fileName ++ obj.fileName⟩
  return result

def readObj (hash : Hash) : IO ByteArray := do
  let addr := git.objDir |>.join (hash.toString.take 2) |>.join (hash.toString.drop 2)
  let content ← FS.readBinFile addr
  return ←inflate content

def readObj' (hash : Hash) : IO FS.Handle := do
  let addr := git.objDir |>.join (hash.toString.take 2) |>.join (hash.toString.drop 2)
  let content ← FS.readBinFile addr
  return ←inflate' content

end Git

-- let mut message : String := ""
--   for i in data do
--     if i ≥ 32 ∧ i < 128 then
--       message := message ++ ⟨[.ofNat i.toNat]⟩
--   logInfo message

def ByteArray.toString (self : ByteArray) : String := .mk <| self.toList.map λ x ↦ .ofNat x.toNat

def test : MetaM Unit := do
  let git : Git := {}
  let hash := (←git.objs)[0]!
  --logInfo $ toMessageData $ hash
  let str : FS.Stream := .ofHandle (←git.readObj' hash)
  logInfo $ repr $ String.fromUTF8? (←str.read 5)
  logInfo $ repr $ String.fromUTF8? (←str.readUntil (·=0))

run_meta test


#check FS.Stream.Buffer
#check FS.Stream.ofBuffer
#check FS.Stream.ofHandle

#check FS.Stream
